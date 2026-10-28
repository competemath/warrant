(** Admission of an inductive block: the one place recursors and their computation rules come from.

    The file's description of the block ({!Claim.block}) is read as a claim. Everything the kernel
    later relies on (the recursor types, the rules, whether the family is recursive or reflexive,
    how many fields a constructor has, whether eliminating into data is allowed, whether K applies,
    how many auxiliary types a nested block needs) is derived here from the types and the
    constructor types alone, and a claim that differs from its derivation rejects the file. The
    auxiliary types made for nested occurrences exist only while the block is being derived: what is
    admitted is the restored form, and a name a file uses can never reach a temporary one. *)

open Verdict
module E = Expr

(* The kernel strips the binder annotations [outParam], [semiOutParam], [optParam] and [autoParam] from the type of
   every local it introduces for a parameter, index or field, so recursor types do not carry them. A constant is
   treated as an annotation only when its definition in the environment is exactly the identity-like one (returns its
   first argument); a file that redefines one of them keeps it as an ordinary constant. *)
let n_out = Name.of_dotted "outParam"
let n_semi = Name.of_dotted "semiOutParam"
let n_opt = Name.of_dotted "optParam"
let n_auto = Name.of_dotted "autoParam"

let returns_first env n arity =
  match Env.find env n with
  | Some { kind = Decl.Def { value; _ }; lparams = [ _ ]; _ } ->
      let rec go v k =
        match (v.E.node, k) with
        | E.Lam (_, b), k when k > 0 -> go b (k - 1)
        | E.BVar i, 0 -> i = arity - 1
        | _ -> false
      in
      go value arity
  | _ -> false

let strip_annotations env e =
  let rec go e =
    match e.E.node with
    | E.App ({ E.node = E.App ({ E.node = E.Const (n, _); _ }, a); _ }, _)
      when (n == n_opt || n == n_auto) && returns_first env n 2 ->
        go a
    | E.App ({ E.node = E.Const (n, _); _ }, a)
      when (n == n_out || n == n_semi) && returns_first env n 1 ->
        go a
    | _ -> e
  in
  go e

let fresh_elim_name lps =
  let candidate i =
    if i = 0 then Name.str Name.anon "u" else Name.str Name.anon ("u_" ^ string_of_int i)
  in
  let rec go i = if List.memq (candidate i) lps then go (i + 1) else candidate i in
  go 0

let rec_name n = Name.str n "rec"

(* A block as the derivation sees it: names and types only. *)
type spec = { tn : Name.t; tty : E.t; sctors : (Name.t * E.t) list }
type derived = { inds : Decl.t list; ctors : Decl.t list; recs : Decl.t list }

type tinfo = {
  k : int;
  s : spec;
  mutable indices : (int * E.t) list;
  mutable major : int * E.t;
  mutable motive : int * E.t;
}

type cinfo = {
  tk : int;
  cname : Name.t;
  cty : E.t;
  cidx : int;
  fields : (int * E.t) list;
  recs : (E.t * (int * E.t) list * int * E.t list) list;
      (** field, telescope, target type, target indices *)
  minor : int * E.t;
}

let mk_pi st fvs body = Tc.mk_binding st E.pi (List.rev fvs) body
let mk_lam st fvs body = Tc.mk_binding st E.lam (List.rev fvs) body

(* ---- derivation ---- *)

let derive env ~lps ~np (specs : spec list) : derived =
  let all = List.map (fun s -> s.tn) specs in
  let ntypes = List.length specs in
  let levels = List.map Level.param lps in
  let ind_const (s : spec) = E.const s.tn levels in
  let has_ind_occ e = E.exists_const (fun n -> List.memq n all) e in
  let tinfos =
    List.mapi
      (fun k s -> { k; s; indices = []; major = (0, E.fvar 0); motive = (0, E.fvar 0) })
      specs
  in
  (* derived flags, syntactic as in the official kernel *)
  let rec scan_rec t =
    match t.E.node with E.Pi (d, b) -> has_ind_occ d || scan_rec b | _ -> false
  in
  let rec scan_refl t =
    match t.E.node with
    | E.Pi (d, b) -> (match d.E.node with E.Pi _ -> has_ind_occ d | _ -> false) || scan_refl b
    | _ -> false
  in
  let all_ctors = List.concat_map (fun s -> s.sctors) specs in
  let is_rec = List.exists (fun (_, t) -> scan_rec t) all_ctors in
  let is_reflexive = List.exists (fun (_, t) -> scan_refl t) all_ctors in
  let ov = Env.overlay env in
  let st = Tc.make ov lps in
  let fresh_local d = Tc.fresh_fvar (strip_annotations env d) in
  Fun.protect
    ~finally:(fun () -> Tc.release ov)
    (fun () ->
      (* 1. the types: a shared telescope of parameters, indices, one result universe *)
      let params = ref [] in
      let res_level = ref None in
      List.iter
        (fun ti ->
          ignore (Tc.check_type st ti.s.tty);
          let rec peel ty i indices =
            match ty.E.node with
            | E.Pi (d, b) ->
                if i < np then
                  begin if ti.k = 0 then begin
                    let id, fv = fresh_local d in
                    params := !params @ [ (id, fv) ];
                    peel (E.instantiate1 b fv) (i + 1) indices
                  end
                  else
                    let pid, pfv = List.nth !params i in
                    if not (Tc.is_def_eq st d (Tc.local_of pid).lty) then
                      reject "parameters of all inductive types must match";
                    peel (E.instantiate1 b pfv) (i + 1) indices
                  end
                else
                  let id, fv = fresh_local d in
                  peel (E.instantiate1 b fv) (i + 1) (indices @ [ (id, fv) ])
            | _ ->
                if i < np then
                  reject "number of parameters mismatch in inductive type %s"
                    (Name.to_string ti.s.tn);
                (ty, indices)
          in
          let rest, indices = peel ti.s.tty 0 [] in
          let l = Tc.ensure_sort st rest in
          (match !res_level with
          | None -> res_level := Some l
          | Some r ->
              if not (Level.equiv r l) then
                reject "mutually inductive types must live in the same universe");
          ti.indices <- indices)
        tinfos;
      let params = !params in
      let param_exprs = List.map snd params in
      let res_level = Option.get !res_level in
      let res_zero = Level.is_zero res_level in
      let is_not_zero = Level.is_never_zero res_level in
      let nindices ti = List.length ti.indices in
      List.iter
        (fun ti ->
          Env.assume ov
            {
              Decl.name = ti.s.tn;
              lparams = lps;
              ty = ti.s.tty;
              kind =
                Decl.Induct
                  {
                    all;
                    ctors = List.map fst ti.s.sctors;
                    nparams = np;
                    nindices = nindices ti;
                    is_rec;
                    is_reflexive;
                    nnested = 0;
                  };
            })
        tinfos;
      (* 2. the constructors *)
      let which_valid_ind_app t =
        let f = E.get_app_fn t in
        let args = E.get_app_args t in
        let rec go = function
          | [] -> None
          | ti :: rest ->
              if
                f == ind_const ti.s
                && List.length args = np + nindices ti
                && List.for_all2
                     (fun a p -> a == p)
                     (List.filteri (fun i _ -> i < np) args)
                     param_exprs
              then Some ti.k
              else go rest
        in
        go tinfos
      in
      let rec check_positivity t =
        let t = Tc.whnf st t in
        if not (has_ind_occ t) then ()
        else
          match t.E.node with
          | E.Pi (d, b) ->
              if has_ind_occ d then
                reject "non-positive occurrence of an inductive type being declared";
              let _, fv = fresh_local d in
              check_positivity (E.instantiate1 b fv)
          | _ -> (
              match which_valid_ind_app t with
              | Some _ -> ()
              | None -> reject "invalid occurrence of an inductive type being declared")
      in
      let cinfos_raw =
        List.concat_map
          (fun ti ->
            List.mapi
              (fun cidx (cname, cty) ->
                ignore (Tc.check_type st cty);
                let rec walk t i fields =
                  match t.E.node with
                  | E.Pi (d, b) ->
                      if i < np then begin
                        let pty = (Tc.local_of (fst (List.nth params i))).lty in
                        if not (Tc.is_def_eq st d pty) then
                          reject "constructor %s: parameters do not match the type's"
                            (Name.to_string cname);
                        walk (E.instantiate1 b (List.nth param_exprs i)) (i + 1) fields
                      end
                      else begin
                        let s = Tc.ensure_sort st (Tc.infer st ~check:true d) in
                        if not (res_zero || Level.leq s res_level <> None) then
                          reject
                            "constructor %s: a field lives in a universe larger than the type's"
                            (Name.to_string cname);
                        check_positivity d;
                        let id, fv = fresh_local d in
                        walk (E.instantiate1 b fv) (i + 1) (fields @ [ (id, fv) ])
                      end
                  | _ ->
                      if i < np then
                        reject "constructor %s: too few parameters" (Name.to_string cname);
                      (t, fields)
                in
                let result, fields = walk cty 0 [] in
                (match which_valid_ind_app result with
                | Some j when j = ti.k -> ()
                | _ -> reject "constructor %s: invalid return type" (Name.to_string cname));
                (ti, cname, cty, cidx, result, fields))
              ti.s.sctors)
          tinfos
      in
      (* 3. the eliminator universe *)
      let elim_only_zero =
        if is_not_zero then false
        else if ntypes > 1 then true
        else
          match cinfos_raw with
          | [] -> false
          | [ (_, _, _, _, result, fields) ] ->
              let result_args = E.get_app_args result in
              List.exists
                (fun (id, fv) ->
                  let s = Tc.ensure_sort st (Tc.infer_only st (Tc.local_of id).lty) in
                  (not (Level.is_zero s)) && not (List.memq fv result_args))
                fields
          | _ -> true
      in
      let elim_level_name = fresh_elim_name lps in
      let elim_level = if elim_only_zero then Level.zero else Level.param elim_level_name in
      let rec_lps = if elim_only_zero then lps else elim_level_name :: lps in
      let rec_levels = List.map Level.param rec_lps in
      List.iter
        (fun ti ->
          let major_ty = E.mk_app (ind_const ti.s) (param_exprs @ List.map snd ti.indices) in
          ti.major <- Tc.fresh_fvar major_ty;
          let motive_ty = mk_pi st (ti.indices @ [ ti.major ]) (E.sort elim_level) in
          ti.motive <- Tc.fresh_fvar motive_ty)
        tinfos;
      let motives = List.map (fun ti -> ti.motive) tinfos in
      let get_indices t =
        match which_valid_ind_app t with
        | Some j -> (j, List.filteri (fun i _ -> i >= np) (E.get_app_args t))
        | None -> reject "internal: not a valid inductive application"
      in
      let ti_of j = List.nth tinfos j in
      let rec_telescope fv_ty =
        let rec go t xs =
          let t = Tc.whnf st t in
          match t.E.node with
          | E.Pi (d, b) ->
              let id, x = fresh_local d in
              go (E.instantiate1 b x) (xs @ [ (id, x) ])
          | _ -> (xs, t)
        in
        let xs, target = go fv_ty [] in
        match which_valid_ind_app target with Some _ -> Some (xs, target) | None -> None
      in
      let cinfos =
        List.map
          (fun (ti, cname, cty, cidx, result, fields) ->
            let recs =
              List.filter_map
                (fun (id, fv) ->
                  match rec_telescope (Tc.local_of id).lty with
                  | Some (xs, target) ->
                      let j, idx = get_indices target in
                      Some (fv, xs, j, idx)
                  | None -> None)
                fields
            in
            let result_indices = snd (get_indices result) in
            let ihs =
              List.map
                (fun (fv, xs, j, idx) ->
                  let c_app =
                    E.mk_app (snd (ti_of j).motive) (idx @ [ E.mk_app fv (List.map snd xs) ])
                  in
                  Tc.fresh_fvar (mk_pi st xs c_app))
                recs
            in
            let ctor_app =
              E.mk_app (E.mk_app (E.const cname levels) param_exprs) (List.map snd fields)
            in
            let c_app = E.mk_app (snd ti.motive) (result_indices @ [ ctor_app ]) in
            let minor_ty = mk_pi st fields (mk_pi st ihs c_app) in
            { tk = ti.k; cname; cty; cidx; fields; recs; minor = Tc.fresh_fvar minor_ty })
          cinfos_raw
      in
      let minors = List.map (fun ci -> ci.minor) cinfos in
      let nminors = List.length minors in
      let k_target =
        ntypes = 1 && res_zero && match cinfos with [ ci ] -> ci.fields = [] | _ -> false
      in
      (* 4. the recursors *)
      let recs =
        List.map
          (fun ti ->
            let rec_ty =
              mk_pi st
                (params @ motives @ minors @ ti.indices @ [ ti.major ])
                (E.mk_app (snd ti.motive) (List.map snd ti.indices @ [ snd ti.major ]))
            in
            let rules =
              List.filter_map
                (fun ci ->
                  if ci.tk <> ti.k then None
                  else
                    let v =
                      List.map
                        (fun (fv, xs, j, idx) ->
                          let rec_app =
                            E.mk_app
                              (E.const (rec_name (ti_of j).s.tn) rec_levels)
                              (param_exprs @ List.map snd motives @ List.map snd minors @ idx
                              @ [ E.mk_app fv (List.map snd xs) ])
                          in
                          mk_lam st xs rec_app)
                        ci.recs
                    in
                    let e_app = E.mk_app (E.mk_app (snd ci.minor) (List.map snd ci.fields)) v in
                    let rhs = mk_lam st (params @ motives @ minors @ ci.fields) e_app in
                    Some { Decl.ctor = ci.cname; nfields = List.length ci.fields; rhs })
                cinfos
            in
            {
              Decl.name = rec_name ti.s.tn;
              lparams = rec_lps;
              ty = rec_ty;
              kind =
                Decl.Rec
                  {
                    rall = all;
                    major_induct = ti.s.tn;
                    rparams = np;
                    rindices = nindices ti;
                    nmotives = ntypes;
                    nminors;
                    rules;
                    k = k_target;
                  };
            })
          tinfos
      in
      let inds =
        List.map
          (fun ti ->
            {
              Decl.name = ti.s.tn;
              lparams = lps;
              ty = ti.s.tty;
              kind =
                Decl.Induct
                  {
                    all;
                    ctors = List.map fst ti.s.sctors;
                    nparams = np;
                    nindices = nindices ti;
                    is_rec;
                    is_reflexive;
                    nnested = 0;
                  };
            })
          tinfos
      in
      let ctors =
        List.map
          (fun ci ->
            {
              Decl.name = ci.cname;
              lparams = lps;
              ty = ci.cty;
              kind =
                Decl.Ctor
                  {
                    induct = (List.nth tinfos ci.tk).s.tn;
                    cidx = ci.cidx;
                    cparams = np;
                    nfields = List.length ci.fields;
                  };
            })
          cinfos
      in
      { inds; ctors; recs })

(* ---- nested occurrences ---- *)

type nested = {
  aux : spec list;  (** the original types followed by the auxiliary ones *)
  jas : (Name.t * E.t * Name.t) list;
      (** auxiliary type, the nested type it stands for (over [params]), its container *)
  param_ids : int array;
  param_fvars : E.t array;
}

let elim_nested env ~lps ~np (specs : spec list) : nested =
  let levels = List.map Level.param lps in
  let block_names = ref (List.map (fun s -> s.tn) specs) in
  let new_types = ref specs in
  let aux_info : (Name.t * E.t * Name.t) list ref = ref [] in
  let ov = Env.overlay env in
  let st = Tc.make ov lps in
  (* the shared parameters, from the first type *)
  let first = List.hd specs in
  let param_ids = Array.make np 0 and param_fvars = Array.make np (E.fvar 0) in
  let rec peel ty i =
    if i < np then
      match ty.E.node with
      | E.Pi (d, b) ->
          let id, fv = Tc.fresh_fvar d in
          param_ids.(i) <- id;
          param_fvars.(i) <- fv;
          peel (E.instantiate1 b fv) (i + 1)
      | _ -> reject "number of parameters mismatch in inductive type %s" (Name.to_string first.tn)
  in
  peel first.tty 0;
  let next_idx = ref 1 in
  let block_has n = List.memq n !block_names in
  let unique_name base =
    let rec go () =
      let cand =
        Name.str (Name.str Name.anon "_nested") (Name.to_string base ^ "_" ^ string_of_int !next_idx)
      in
      incr next_idx;
      if Env.mem env cand || block_has cand || List.exists (fun (n, _, _) -> n == cand) !aux_info
      then go ()
      else cand
    in
    go ()
  in
  let to_params (e : E.t) (as_ : (int * E.t) list) =
    E.instantiate_rev (E.abstract e (Array.of_list (List.map fst as_))) param_fvars
  in
  let nested_app (e : E.t) =
    match e.node with
    | E.App _ -> (
        match (E.get_app_fn e).node with
        | E.Const (j, _) -> (
            match Env.find env j with
            | Some { kind = Decl.Induct ji; _ } ->
                let args = E.get_app_args e in
                if ji.nparams > List.length args then None
                else
                  let ds = List.filteri (fun i _ -> i < ji.nparams) args in
                  let loose = List.exists (fun (a : E.t) -> a.lbr > 0) ds in
                  let nested = List.exists (fun d -> E.exists_const block_has d) ds in
                  if not nested then None
                  else if loose then
                    reject
                      "invalid nested inductive datatype %s: its parameters cannot contain local \
                       variables"
                      (Name.to_string j)
                  else Some ji
            | _ -> None)
        | _ -> None)
    | _ -> None
  in
  let instantiate_pi_params (e : E.t) n (params : E.t list) =
    let rec strip e i =
      if i = n then e
      else
        match e.E.node with
        | E.Pi (_, b) -> strip b (i + 1)
        | _ -> reject "ill-formed nested inductive declaration"
    in
    E.instantiate_rev (strip e 0) (Array.of_list params)
  in
  let replace_if_nested (as_ : (int * E.t) list) (t : E.t) : E.t option =
    match nested_app t with
    | None -> None
    | Some ji -> (
        let fn = E.get_app_fn t and args = E.get_app_args t in
        let i_name, i_lvls = match fn.node with E.Const (n, l) -> (n, l) | _ -> assert false in
        let ds = List.filteri (fun i _ -> i < ji.nparams) args in
        let rest = List.filteri (fun i _ -> i >= ji.nparams) args in
        let ias = to_params (E.mk_app fn ds) as_ in
        let a_exprs = List.map snd as_ in
        match List.find_opt (fun (_, e, _) -> e == ias) !aux_info with
        | Some (aux_name, _, _) -> Some (E.mk_app (E.mk_app (E.const aux_name levels) a_exprs) rest)
        | None ->
            let result = ref None in
            List.iter
              (fun j_name ->
                match Env.find env j_name with
                | Some ({ kind = Decl.Induct jv; _ } as jd) ->
                    let jas = E.mk_app (E.const j_name i_lvls) ds in
                    let aux_name = unique_name j_name in
                    let aux_ty =
                      E.inst_lparams jd.lparams i_lvls jd.ty |> fun t ->
                      instantiate_pi_params t ji.nparams ds |> mk_pi st as_
                    in
                    aux_info := !aux_info @ [ (aux_name, to_params jas as_, j_name) ];
                    block_names := !block_names @ [ aux_name ];
                    if j_name == i_name then
                      result := Some (E.mk_app (E.mk_app (E.const aux_name levels) a_exprs) rest);
                    let ctors =
                      List.map
                        (fun cn ->
                          match Env.find env cn with
                          | Some cd ->
                              let cty =
                                E.inst_lparams cd.lparams i_lvls cd.ty |> fun t ->
                                instantiate_pi_params t ji.nparams ds |> mk_pi st as_
                              in
                              (Name.replace_prefix cn j_name aux_name, cty)
                          | None -> reject "nested inductive: unknown constructor")
                        jv.ctors
                    in
                    new_types := !new_types @ [ { tn = aux_name; tty = aux_ty; sctors = ctors } ]
                | _ -> reject "nested inductive: unknown inductive type")
              ji.all;
            !result)
  in
  let i = ref 0 in
  while !i < List.length !new_types do
    let s = List.nth !new_types !i in
    let sctors =
      List.map
        (fun (cn, cty) ->
          (* open the parameters of this constructor *)
          let rec open_ params t j =
            if j = np then (List.rev params, t)
            else
              match t.E.node with
              | E.Pi (d, b) ->
                  let id, fv = Tc.fresh_fvar d in
                  open_ ((id, fv) :: params) (E.instantiate1 b fv) (j + 1)
              | _ -> reject "constructor %s: too few parameters" (Name.to_string cn)
          in
          let as_, body = open_ [] cty 0 in
          let body' = E.replace (fun _ t -> replace_if_nested as_ t) body in
          (cn, if body' == body then cty else mk_pi st as_ body'))
        s.sctors
    in
    new_types := List.mapi (fun k t -> if k = !i then { s with sctors } else t) !new_types;
    incr i
  done;
  Tc.release ov;
  { aux = !new_types; jas = !aux_info; param_ids; param_fvars }

(* Rewrite a derived term back to the original types: auxiliary types become the nested types they stand for,
   auxiliary constructors their container's, auxiliary recursors the [rec_<i>] of the first type. *)
let restore env ~lps ~np (nst : nested) (aux_ctor_owner : Name.t -> Name.t option)
    (rec_map : (Name.t * Name.t) list) (e : E.t) : E.t =
  let ov = Env.overlay env in
  let st = Tc.make ov lps in
  let is_pi = match e.node with E.Pi _ -> true | _ -> false in
  let rec open_ as_ t j =
    if j = np then (List.rev as_, t)
    else
      match t.E.node with
      | E.Pi (d, b) | E.Lam (d, b) ->
          let id, fv = Tc.fresh_fvar d in
          open_ ((id, fv) :: as_) (E.instantiate1 b fv) (j + 1)
      | _ -> reject "internal: restoring a term without its parameters"
  in
  let as_, body = open_ [] e 0 in
  let nested_of aux = List.find_opt (fun (n, _, _) -> n == aux) nst.jas in
  let with_params (nested : E.t) =
    E.instantiate_rev (E.abstract nested nst.param_ids) (Array.of_list (List.map snd as_))
  in
  let f _ (t : E.t) =
    match t.node with
    | E.Const (n, ls) when List.mem_assq n rec_map -> Some (E.const (List.assq n rec_map) ls)
    | _ -> (
        let fn = E.get_app_fn t in
        match fn.node with
        | E.Const (n, _) -> (
            match nested_of n with
            | Some (_, jas, _) ->
                let args = E.get_app_args t in
                if List.length args < np then
                  reject "internal: auxiliary type applied to too few arguments";
                Some (E.mk_app (with_params jas) (List.filteri (fun i _ -> i >= np) args))
            | None -> (
                match aux_ctor_owner n with
                | Some aux -> (
                    match nested_of aux with
                    | Some (_, jas, _) ->
                        let args = E.get_app_args t in
                        if List.length args < np then
                          reject "internal: auxiliary constructor applied to too few arguments";
                        let nested = with_params jas in
                        let i_fn = E.get_app_fn nested and i_args = E.get_app_args nested in
                        let i_name, i_lvls =
                          match i_fn.node with
                          | E.Const (m, l) -> (m, l)
                          | _ -> reject "internal: nested type"
                        in
                        let new_fn = E.const (Name.replace_prefix n aux i_name) i_lvls in
                        Some
                          (E.mk_app (E.mk_app new_fn i_args)
                             (List.filteri (fun i _ -> i >= np) args))
                    | None -> None)
                | None -> None))
        | _ -> None)
  in
  let body' = E.replace f body in
  let r = (if is_pi then mk_pi else mk_lam) st as_ body' in
  Tc.release ov;
  r

(* the head of the type of the major premise, as the kernel reads it off a recursor's type *)
let major_induct_of (r : Decl.recursor) (ty : E.t) =
  let n = r.rparams + r.nmotives + r.nminors + r.rindices in
  let rec go t i =
    match t.E.node with
    | E.Pi (d, b) -> if i = n then E.get_app_fn d else go b (i + 1)
    | _ -> reject "recursor type is not a telescope"
  in
  match (go ty 0).node with
  | E.Const (c, _) -> c
  | _ -> reject "recursor: the major premise is not an inductive type"

let admit env (blk : Claim.block) : Evidence.Ind_ok.t =
  let types = blk.types in
  if types = [] then reject "empty inductive block";
  let t0 = List.hd types in
  let lps = t0.lparams and np = t0.nparams in
  let all = List.map (fun (t : Claim.ind_type) -> t.name) types in
  List.iter
    (fun (t : Claim.ind_type) ->
      if t.lparams <> lps then reject "inductive block: universe parameters differ between types";
      if t.nparams <> np then reject "inductive block: number of parameters differs between types";
      if t.all <> all then reject "inductive block: 'all' is not the block";
      if t.unsafe then decline "unsafe inductive types")
    types;
  if List.exists (fun (c : Claim.ctor) -> c.cunsafe) blk.ctor_decls then
    decline "unsafe constructors";
  if List.exists (fun (r : Claim.recursor) -> r.runsafe) blk.recs then decline "unsafe recursors";
  (* constructors: exactly those listed, each by one type, in order *)
  let ctors_of (t : Claim.ind_type) =
    List.mapi
      (fun i n ->
        match List.filter (fun (c : Claim.ctor) -> c.cname == n) blk.ctor_decls with
        | [ c ] ->
            if c.induct != t.name then
              reject "constructor %s is listed under another type" (Name.to_string n);
            if c.cidx <> i then reject "constructor %s has the wrong index" (Name.to_string n);
            if c.clparams <> lps then
              reject "constructor %s: universe parameters differ" (Name.to_string n);
            if c.cnparams <> np then
              reject "constructor %s: number of parameters differs" (Name.to_string n);
            c
        | [] -> reject "constructor %s is listed but not declared" (Name.to_string n)
        | _ -> reject "constructor %s is declared twice" (Name.to_string n))
      t.ctors
  in
  let claimed_ctors = List.concat_map ctors_of types in
  let listed = List.map (fun (c : Claim.ctor) -> c.cname) claimed_ctors in
  List.iter
    (fun (c : Claim.ctor) ->
      if not (List.memq c.cname listed) then
        reject "constructor %s belongs to no type of its block" (Name.to_string c.cname))
    blk.ctor_decls;
  let specs =
    List.map
      (fun (t : Claim.ind_type) ->
        {
          tn = t.name;
          tty = t.ty;
          sctors = List.map (fun (c : Claim.ctor) -> (c.cname, c.cty)) (ctors_of t);
        })
      types
  in
  let nst = elim_nested env ~lps ~np specs in
  let n_orig = List.length specs in
  let n_aux = List.length nst.aux - n_orig in
  let d = derive env ~lps ~np nst.aux in
  let orig_names = all in
  let first_rec = rec_name (List.hd orig_names) in
  (* the final declarations *)
  let inds, ctors, recs =
    if n_aux = 0 then (d.inds, d.ctors, d.recs)
    else begin
      let aux_names = List.filteri (fun i _ -> i >= n_orig) nst.aux |> List.map (fun s -> s.tn) in
      let rec_map =
        List.mapi
          (fun i n ->
            (rec_name n, Name.str (Name.prefix first_rec) ("rec_" ^ string_of_int (i + 1))))
          aux_names
      in
      let aux_ctor_owner c =
        List.find_map
          (fun (dc : Decl.t) ->
            match dc.kind with
            | Decl.Ctor ci when dc.name == c && List.memq ci.induct aux_names -> Some ci.induct
            | _ -> None)
          d.ctors
      in
      let restore = restore env ~lps ~np nst aux_ctor_owner rec_map in
      let inds =
        List.filter_map
          (fun (dd : Decl.t) ->
            if not (List.memq dd.name orig_names) then None
            else
              match dd.kind with
              | Decl.Induct i ->
                  Some { dd with kind = Decl.Induct { i with all = orig_names; nnested = n_aux } }
              | _ -> assert false)
          d.inds
      in
      let ctors =
        List.filter_map
          (fun (dd : Decl.t) ->
            match dd.kind with
            | Decl.Ctor ci when List.memq ci.induct orig_names ->
                Some { dd with ty = restore dd.ty }
            | _ -> None)
          d.ctors
      in
      let recs =
        List.map
          (fun (dd : Decl.t) ->
            match dd.kind with
            | Decl.Rec r ->
                let name =
                  match List.assq_opt dd.name rec_map with Some n -> n | None -> dd.name
                in
                let ty = restore dd.ty in
                let rules =
                  List.map
                    (fun (ru : Decl.rule) ->
                      let ctor =
                        match aux_ctor_owner ru.ctor with
                        | Some aux -> (
                            match List.find_opt (fun (n, _, _) -> n == aux) nst.jas with
                            | Some (_, jas, _) -> (
                                match (E.get_app_fn jas).node with
                                | E.Const (jn, _) -> Name.replace_prefix ru.ctor aux jn
                                | _ -> ru.ctor)
                            | None -> ru.ctor)
                        | None -> ru.ctor
                      in
                      { ru with ctor; rhs = restore ru.rhs })
                    r.rules
                in
                { dd with name; ty; kind = Decl.Rec { r with rall = orig_names; rules } }
            | _ -> assert false)
          d.recs
      in
      (inds, ctors, recs)
    end
  in
  (* the major premise's type of each recursor, read off the restored type *)
  let recs =
    List.map
      (fun (dd : Decl.t) ->
        match dd.kind with
        | Decl.Rec r ->
            { dd with kind = Decl.Rec { r with major_induct = major_induct_of r dd.ty } }
        | _ -> dd)
      recs
  in
  (* the claims against the derivation *)
  List.iter2
    (fun (t : Claim.ind_type) (dd : Decl.t) ->
      match dd.kind with
      | Decl.Induct i ->
          let nm = Name.to_string t.name in
          if t.is_rec <> i.is_rec then reject "claimed isRec of %s differs from the derivation" nm;
          if t.is_reflexive <> i.is_reflexive then
            reject "claimed isReflexive of %s differs from the derivation" nm;
          if t.nnested <> i.nnested then
            reject "claimed numNested of %s differs from the derivation" nm;
          if t.nindices <> i.nindices then
            reject "claimed numIndices of %s differs from the derivation" nm
      | _ -> assert false)
    types inds;
  List.iter
    (fun (c : Claim.ctor) ->
      match List.find_opt (fun (dd : Decl.t) -> dd.name == c.cname) ctors with
      | Some { kind = Decl.Ctor ci; ty; _ } ->
          if c.nfields <> ci.nfields then
            reject "constructor %s: claimed number of fields differs from the derivation"
              (Name.to_string c.cname);
          if c.cty != ty then
            reject "constructor %s: its type differs from the derivation" (Name.to_string c.cname)
      | _ -> reject "internal: constructor %s was not derived" (Name.to_string c.cname))
    claimed_ctors;
  let derived_names = List.map (fun (dd : Decl.t) -> dd.name) recs in
  List.iter
    (fun (r : Claim.recursor) ->
      if not (List.memq r.rname derived_names) then
        reject "recursor %s is not the recursor of any type of its block" (Name.to_string r.rname))
    blk.recs;
  List.iter
    (fun (dd : Decl.t) ->
      match List.filter (fun (r : Claim.recursor) -> r.rname == dd.name) blk.recs with
      | [ r ] -> (
          match dd.kind with
          | Decl.Rec dr ->
              let nm = Name.to_string dd.name in
              if r.rlparams <> dd.lparams then
                reject "%s: universe parameters differ from the derivation" nm;
              if r.rty != dd.ty then
                reject "%s: the type differs from the derivation\n claimed:  %s\n derived:  %s" nm
                  (E.to_string r.rty) (E.to_string dd.ty);
              if r.rall <> orig_names then reject "%s: 'all' differs from the derivation" nm;
              if
                r.rnparams <> dr.rparams || r.rnindices <> dr.rindices || r.nmotives <> dr.nmotives
                || r.nminors <> dr.nminors
              then
                reject "%s: parameter, index, motive or minor counts differ from the derivation" nm;
              if r.k <> dr.k then reject "%s: the K flag differs from the derivation" nm;
              if List.length r.rules <> List.length dr.rules then
                reject "%s: number of rules differs from the derivation" nm;
              List.iter2
                (fun (cr : Claim.rule) (ru : Decl.rule) ->
                  if cr.ctor != ru.ctor || cr.nfields <> ru.nfields || cr.rhs != ru.rhs then
                    reject "%s: a computation rule differs from the derivation" nm)
                r.rules dr.rules
          | _ -> assert false)
      | [] -> reject "recursor %s is derived but missing from the file" (Name.to_string dd.name)
      | _ -> reject "recursor %s is declared twice" (Name.to_string dd.name))
    recs;
  Evidence.Mint.ind_ok ~env:(Env.id env) (inds @ ctors @ recs)
