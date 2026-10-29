(** The type checker: inference, weak-head normalisation and definitional equality.

    Two entry points mint evidence ({!check_type}, {!check_typing}, {!check_conv}, {!check_prop});
    everything else here answers bare questions about terms that were themselves admitted, and never
    produces a fact the environment would accept. *)

open Verdict
module E = Expr

type expr = E.t = private {
  id : int;
  node : E.node;
  lbr : int;
  has_fvar : bool;
  maxfv : int;
  has_lparam : bool;
}

type local = { lty : E.t; lval : E.t option }

(* Local contexts are global: fvar ids are never reused, and the type of an fvar never changes. *)
let lctx : (int, local) Hashtbl.t = Hashtbl.create 1024
let fvar_counter = ref 0

let fresh_fvar ?value ty =
  incr fvar_counter;
  let id = !fvar_counter in
  Hashtbl.replace lctx id { lty = ty; lval = value };
  (id, E.fvar id)

let local_of id =
  match Hashtbl.find_opt lctx id with Some l -> l | None -> reject "unknown free variable %d" id

(* A term is closed up to let-bound variables when each of its free variables stands for a value that is itself closed
   up to let-bound variables: unfolding them all gives a closed term. Fvar ids are never reused, so the answer for an id
   never changes. *)
let valued : (int, bool) Hashtbl.t = Hashtbl.create 256

let rec closed_modulo_lets (e : E.t) =
  (not e.has_fvar)
  || E.for_all_fvars
       (fun id ->
         match Hashtbl.find_opt valued id with
         | Some b -> b
         | None ->
             (* a variable under test counts as unvalued while its own value is examined (no value mentions it, but
                this keeps the recursion total) *)
             Hashtbl.replace valued id false;
             let b =
               match (local_of id).lval with Some v -> closed_modulo_lets v | None -> false
             in
             Hashtbl.replace valued id b;
             b)
       e

(* A cache for results about terms. A term with free variables is cached under the largest free variable it contains:
   when the binder that introduced that variable is closed, the whole table goes, because no later term can contain it. *)
type 'a cache = { global : (int, 'a) Hashtbl.t; local : (int, (int, 'a) Hashtbl.t) Hashtbl.t }

let new_cache () = { global = Hashtbl.create 4096; local = Hashtbl.create 64 }

let cfind c (e : E.t) =
  if e.maxfv = 0 then Hashtbl.find_opt c.global e.id
  else
    match Hashtbl.find_opt c.local e.maxfv with Some t -> Hashtbl.find_opt t e.id | None -> None

let cadd c (e : E.t) v =
  if e.maxfv = 0 then Hashtbl.replace c.global e.id v
  else
    let t =
      match Hashtbl.find_opt c.local e.maxfv with
      | Some t -> t
      | None ->
          let t = Hashtbl.create 16 in
          Hashtbl.add c.local e.maxfv t;
          t
    in
    Hashtbl.replace t e.id v

type caches = {
  infer_only : E.t cache;
  whnf_core : E.t cache;
  whnf : E.t cache;
  eq_ok : (int * int, unit) Hashtbl.t;
  eq_fail : (int * int, unit) Hashtbl.t;
}

let new_caches () =
  {
    infer_only = new_cache ();
    whnf_core = new_cache ();
    whnf = new_cache ();
    eq_ok = Hashtbl.create 4096;
    eq_fail = Hashtbl.create 4096;
  }

(* Caches hold results about terms of one environment; an environment only grows, so entries stay valid. An overlay
   gets its own. *)
let cache_tbl : (int, caches) Hashtbl.t = Hashtbl.create 16

let caches_of env =
  let id = Env.id env in
  match Hashtbl.find_opt cache_tbl id with
  | Some c -> c
  | None ->
      let c = new_caches () in
      Hashtbl.add cache_tbl id c;
      c

let release env = Hashtbl.remove cache_tbl (Env.id env)

type st = {
  env : Env.t;
  lparams : Name.t list;
  allow_unsafe : bool;
      (** set only while the type of an unsafe or partial declaration is checked *)
  c : caches;
  check_cache : E.t cache;
}

let make ?(allow_unsafe = false) env lparams =
  { env; lparams; allow_unsafe; c = caches_of env; check_cache = new_cache () }

(* the binder that introduced these variables is closed: nothing can mention them again *)
let drop_locals st ids =
  List.iter
    (fun id ->
      Hashtbl.remove st.c.infer_only.local id;
      Hashtbl.remove st.c.whnf_core.local id;
      Hashtbl.remove st.c.whnf.local id;
      Hashtbl.remove st.check_cache.local id;
      Hashtbl.remove lctx id)
    ids

let env st = st.env

(* Work budget: a file that makes the checker diverge is declined, never accepted. *)
let fuel = ref 0
let trace = Sys.getenv_opt "WARRANT_TRACE" <> None

(* The two limits below can be lowered from the environment, for the tests only (see Knobs). *)
let default_fuel = Knobs.limit "WARRANT_FUEL" 400_000_000

let tick () =
  decr fuel;
  if !fuel < 0 then decline "work budget exhausted"

let nm = Name.of_dotted
let n_nat = nm "Nat"
let n_nat_zero = nm "Nat.zero"
let n_nat_succ = nm "Nat.succ"
let n_string = nm "String"
let n_string_mk = nm "String.mk"
let n_char = nm "Char"
let n_char_of_nat = nm "Char.ofNat"
let n_list_nil = nm "List.nil"
let n_list_cons = nm "List.cons"
let n_bool_true = nm "Bool.true"
let n_bool_false = nm "Bool.false"
let find_decl st n = Env.find st.env n

(* ---- small helpers ---- *)

let mk_const n = E.const n []
let nat_type = mk_const n_nat
let nat_ok st = Prim.genuine st.env "Nat"
let is_const_named e n = match e.E.node with E.Const (m, _) -> m == n | _ -> false

let rec beta_core f args =
  (* apply [f] to [args], contracting leading lambdas *)
  match (f.E.node, args) with
  | E.Lam _, _ :: _ ->
      let rec peel body substs args =
        match (body.E.node, args) with
        | E.Lam (_, b), a :: rest -> peel b (a :: substs) rest
        | _ -> (body, substs, args)
      in
      let body, substs, rest = peel f [] args in
      let r = E.instantiate_rev body (Array.of_list (List.rev substs)) in
      beta_core r rest
  | _ -> E.mk_app f args

let unfoldable st e =
  match (E.get_app_fn e).E.node with
  | E.Const (n, ls) -> (
      match find_decl st n with
      | Some ({ kind = Decl.Def _ | Decl.Thm _; _ } as d)
        when List.length ls = List.length d.lparams ->
          Some d
      | _ -> None)
  | _ -> None

let hints_of (d : Decl.t) = match d.kind with Decl.Def { hints; _ } -> hints | _ -> Decl.Opaque

let unfold_definition st e =
  match unfoldable st e with
  | None -> None
  | Some d -> (
      match (E.get_app_fn e).E.node with
      | E.Const (_, ls) when List.length ls = List.length d.lparams ->
          let value =
            match d.kind with
            | Decl.Def { value; _ } | Decl.Thm { value } -> value
            | _ -> assert false
          in
          let v = E.inst_lparams d.lparams ls value in
          Some (beta_core v (E.get_app_args e))
      | _ -> None)

(* ---- structure-like inductives ---- *)

let induct_of st n =
  match find_decl st n with Some { kind = Decl.Induct i; _ } -> Some i | _ -> None

let is_structure_like st n =
  match induct_of st n with
  | Some i -> List.length i.ctors = 1 && i.nindices = 0 && not i.is_rec
  | None -> false

let ctor_of st n = match find_decl st n with Some { kind = Decl.Ctor c; _ } -> Some c | _ -> None

(* ---- literals ---- *)

let nat_lit_to_ctor st z =
  if not (nat_ok st) then
    reject "natural number literal: the environment's Nat is not the genuine one";
  if Z.equal z Z.zero then mk_const n_nat_zero else E.app (mk_const n_nat_succ) (E.nat (Z.pred z))

(* The meaning of a string literal is the application of the environment's own list-to-string function to the list of
   its characters: [String.ofList] in current toolchains, [String.mk] in older ones. Whichever is used must have type
   [List Char -> String]; a file without one has no string literals. *)
let n_string_of_list = nm "String.ofList"

let string_ctor_name st =
  let ok n =
    match Env.find st.env n with
    | Some d ->
        d.lparams = []
        && d.ty
           == E.pi
                (E.app (E.const (nm "List") [ Level.zero ]) (mk_const n_char))
                (mk_const n_string)
    | None -> false
  in
  if ok n_string_of_list then n_string_of_list
  else if ok n_string_mk then n_string_mk
  else
    reject
      "string literal: the environment has no String.ofList or String.mk of type List Char -> \
       String"

let is_string_ctor e = is_const_named e n_string_mk || is_const_named e n_string_of_list

let string_lit_to_ctor st s =
  let char_ty = mk_const n_char in
  let u0 = [ Level.zero ] in
  let nil = E.app (E.const n_list_nil u0) char_ty in
  let cons = E.app (E.const n_list_cons u0) char_ty in
  (* decode UTF-8 *)
  let cps = ref [] in
  let d = String.get_utf_8_uchar in
  let i = ref 0 in
  while !i < String.length s do
    let u = d s !i in
    cps := Uchar.to_int (Uchar.utf_decode_uchar u) :: !cps;
    i := !i + Uchar.utf_decode_length u
  done;
  let lst =
    List.fold_left
      (fun acc cp -> E.mk_app cons [ E.app (mk_const n_char_of_nat) (E.nat (Z.of_int cp)); acc ])
      nil !cps
  in
  E.app (mk_const (string_ctor_name st)) lst

(* ---- reduction ---- *)

let nat_binops : (Name.t * (Z.t -> Z.t -> E.t)) list =
  let lit f a b = E.nat (f a b) in
  let bool b = mk_const (if b then n_bool_true else n_bool_false) in
  let max_pow = 1 lsl 24 in
  let max_bits = 1 lsl 28 in
  [
    (nm "Nat.add", lit Z.add);
    (nm "Nat.sub", lit (fun a b -> if Z.lt a b then Z.zero else Z.sub a b));
    (nm "Nat.mul", lit Z.mul);
    (nm "Nat.div", lit (fun a b -> if Z.equal b Z.zero then Z.zero else Z.div a b));
    (nm "Nat.mod", lit (fun a b -> if Z.equal b Z.zero then a else Z.rem a b));
    (nm "Nat.gcd", lit Z.gcd);
    (nm "Nat.beq", fun a b -> bool (Z.equal a b));
    (nm "Nat.ble", fun a b -> bool (Z.leq a b));
    (nm "Nat.land", lit Z.logand);
    (nm "Nat.lor", lit Z.logor);
    (nm "Nat.xor", lit Z.logxor);
    ( nm "Nat.shiftLeft",
      fun a b ->
        if Z.gt b (Z.of_int max_pow) || Z.numbits a + Z.to_int b > max_bits then
          decline "shiftLeft: result too large"
        else E.nat (Z.shift_left a (Z.to_int b)) );
    ( nm "Nat.shiftRight",
      fun a b ->
        (* shifting by more than the number of bits leaves nothing *)
        if Z.gt b (Z.of_int (Z.numbits a)) then E.nat Z.zero
        else E.nat (Z.shift_right a (Z.to_int b)) );
    ( nm "Nat.pow",
      fun a b ->
        if Z.gt b (Z.of_int max_pow) || Z.numbits a * Z.to_int b > max_bits then
          decline "pow: result too large"
        else E.nat (Z.pow a (Z.to_int b)) );
  ]

let nat_binop_tbl : (Name.t * (Z.t -> Z.t -> E.t)) list = nat_binops
let n_nat_log2 = nm "Nat.log2"
let log2 z = if Z.leq z Z.zero then Z.zero else Z.of_int (Z.log2 z)

(* literal, possibly spelled [Nat.zero] *)
let nat_lit_ext st e =
  match e.E.node with
  | E.Nat z -> if nat_ok st then Some z else None
  | E.Const (n, []) when n == n_nat_zero && nat_ok st -> Some Z.zero
  | _ -> None

let rec whnf_core ?(cheap_rec = false) ?(cheap_proj = false) st e =
  match e.E.node with
  | E.BVar _ | E.Sort _ | E.Pi _ | E.Lam _ | E.Nat _ | E.Str _ | E.Const _ -> e
  | E.Let (_, v, b) -> whnf_core ~cheap_rec ~cheap_proj st (E.instantiate1 b v)
  | E.FVar id -> (
      match (local_of id).lval with Some v -> whnf_core ~cheap_rec ~cheap_proj st v | None -> e)
  | E.App _ | E.Proj _ -> (
      let cacheable = (not cheap_rec) && not cheap_proj in
      match if cacheable then cfind st.c.whnf_core e else None with
      | Some r -> r
      | None ->
          tick ();
          let r =
            match e.node with
            | E.Proj (_, i, s) -> (
                match reduce_proj st ~cheap_rec ~cheap_proj i s with
                | Some r -> whnf_core ~cheap_rec ~cheap_proj st r
                | None -> e)
            | _ -> (
                let f0 = E.get_app_fn e in
                let args = E.get_app_args e in
                let f = whnf_core ~cheap_rec ~cheap_proj st f0 in
                match f.node with
                | E.Lam _ -> whnf_core ~cheap_rec ~cheap_proj st (beta_core f args)
                | _ -> (
                    if f != f0 then whnf_core ~cheap_rec ~cheap_proj st (E.mk_app f args)
                    else
                      match reduce_rec st ~cheap_rec ~cheap_proj e with
                      | Some r -> whnf_core ~cheap_rec ~cheap_proj st r
                      | None -> e))
          in
          if cacheable then cadd st.c.whnf_core e r;
          r)

and reduce_proj st ~cheap_rec ~cheap_proj i s =
  let s' = if cheap_proj then whnf_core ~cheap_rec ~cheap_proj st s else whnf st s in
  let s' = match s'.node with E.Str str -> whnf st (string_lit_to_ctor st str) | _ -> s' in
  match (E.get_app_fn s').node with
  | E.Const (c, _) -> (
      match ctor_of st c with
      | Some ci ->
          let args = E.get_app_args s' in
          List.nth_opt args (ci.cparams + i)
      | None -> None)
  | _ -> None

and reduce_rec st ~cheap_rec ~cheap_proj e =
  match (E.get_app_fn e).node with
  | E.Const (n, ls) -> (
      match find_decl st n with
      | Some { kind = Decl.Rec r; lparams; _ } ->
          reduce_recursor st ~cheap_rec ~cheap_proj e r lparams ls
      | Some { kind = Decl.Quot q; _ } -> reduce_quot st e q
      | _ -> None)
  | _ -> None

and reduce_quot st e q =
  let mk_pos, arg_pos =
    match q with Decl.QLift -> (5, 3) | Decl.QInd -> (4, 3) | Decl.QType | Decl.QCtor -> (-1, -1)
  in
  if mk_pos < 0 then None
  else
    let args = Array.of_list (E.get_app_args e) in
    if Array.length args <= mk_pos then None
    else
      let mk = whnf st args.(mk_pos) in
      let is_mk =
        match (E.get_app_fn mk).node with
        | E.Const (c, _) -> (
            match find_decl st c with Some { kind = Decl.Quot Decl.QCtor; _ } -> true | _ -> false)
        | _ -> false
      in
      if (not is_mk) || E.get_app_num_args mk <> 3 then None
      else
        let a = List.nth (E.get_app_args mk) 2 in
        let r = E.app args.(arg_pos) a in
        let arity = mk_pos + 1 in
        let extra = Array.to_list (Array.sub args arity (Array.length args - arity)) in
        Some (E.mk_app r extra)

and reduce_recursor st ~cheap_rec ~cheap_proj e (r : Decl.recursor) rec_lparams ls =
  let args = Array.of_list (E.get_app_args e) in
  let major_idx = r.rparams + r.nmotives + r.nminors + r.rindices in
  if Array.length args <= major_idx then None
  else if List.length ls <> List.length rec_lparams then None
  else begin
    let major = args.(major_idx) in
    let major =
      if r.k then match to_ctor_when_k st r major with Some c -> c | None -> major else major
    in
    let major = if cheap_rec then whnf_core ~cheap_rec ~cheap_proj st major else whnf st major in
    let major =
      match major.node with
      | E.Nat z -> nat_lit_to_ctor st z
      | E.Str s -> whnf st (string_lit_to_ctor st s)
      | _ -> to_ctor_when_structure st r.major_induct major
    in
    match (E.get_app_fn major).node with
    | E.Const (c, _) -> (
        match List.find_opt (fun (ru : Decl.rule) -> ru.ctor == c) r.rules with
        | None -> None
        | Some ru ->
            let margs = E.get_app_args major in
            let nm = List.length margs in
            if ru.nfields > nm then None
            else begin
              let rhs = E.inst_lparams rec_lparams ls ru.rhs in
              let pre = r.rparams + r.nmotives + r.nminors in
              let rhs = E.mk_app rhs (Array.to_list (Array.sub args 0 pre)) in
              let fields = List.filteri (fun i _ -> i >= nm - ru.nfields) margs in
              let rhs = E.mk_app rhs fields in
              let extra =
                Array.to_list (Array.sub args (major_idx + 1) (Array.length args - major_idx - 1))
              in
              Some (E.mk_app rhs extra)
            end)
    | _ -> None
  end

and to_ctor_when_k st (r : Decl.recursor) e =
  let app_type = whnf st (infer_only st e) in
  match (E.get_app_fn app_type).node with
  | E.Const (i, ls) when i == r.major_induct -> (
      match induct_of st i with
      | Some { ctors = c :: _; _ } ->
          let args = E.get_app_args app_type in
          let params = List.filteri (fun k _ -> k < r.rparams) args in
          let ctor_app = E.mk_app (E.const c ls) params in
          let new_type = infer_only st ctor_app in
          if is_def_eq st app_type new_type then Some ctor_app else None
      | _ -> None)
  | _ -> None

and to_ctor_when_structure st ind_name e =
  if not (is_structure_like st ind_name) then e
  else
    match (E.get_app_fn e).node with
    | E.Const (c, _) when ctor_of st c <> None -> e
    | _ -> (
        let raw_type = infer_only st e in
        let e_type = whnf st raw_type in
        match (E.get_app_fn e_type).node with
        | E.Const (i, ls) when i == ind_name -> (
            if is_prop_type st raw_type || is_prop_type st e_type then e
            else
              match induct_of st i with
              | Some { ctors = [ c ]; nparams; _ } -> (
                  match ctor_of st c with
                  | Some ci ->
                      let params = List.filteri (fun k _ -> k < nparams) (E.get_app_args e_type) in
                      let fields = List.init ci.nfields (fun k -> E.proj i k e) in
                      E.mk_app (E.mk_app (E.const c ls) params) fields
                  | None -> e)
              | _ -> e)
        | _ -> e)

(* No guard on free variables here: a let-bound variable stands for its (closed) value, and the arguments are reduced
   with [whnf], which unfolds it. The kernel's [reduce_nat] has none either; its fvar test is in the lazy delta loop. *)
and reduce_nat st e =
  match e.node with
  | E.App (f, a) -> (
      match f.node with
      | E.Const (n, _) when n == n_nat_succ && nat_ok st -> (
          match nat_lit_ext st (whnf st a) with Some z -> Some (E.nat (Z.succ z)) | None -> None)
      | E.Const (n, _) when n == n_nat_log2 && Prim.genuine st.env "Nat.log2" -> (
          match nat_lit_ext st (whnf st a) with Some z -> Some (E.nat (log2 z)) | None -> None)
      | E.App (g, a1) -> (
          match g.node with
          | E.Const (n, _) -> (
              match List.assq_opt n nat_binop_tbl with
              | Some op
                when Prim.genuine st.env (Name.to_string n)
                     &&
                     match Name.to_string n with
                     | "Nat.beq" | "Nat.ble" -> Prim.genuine st.env "Bool"
                     | _ -> true -> (
                  match (nat_lit_ext st (whnf st a1), nat_lit_ext st (whnf st a)) with
                  | Some x, Some y -> Some (op x y)
                  | _ -> None)
              | _ -> None)
          | _ -> None)
      | _ -> None)
  | _ -> None

and whnf st e =
  match e.node with
  | E.BVar _ | E.Sort _ | E.Pi _ | E.Lam _ | E.Nat _ | E.Str _ -> e
  | _ -> (
      match cfind st.c.whnf e with
      | Some r -> r
      | None ->
          let rec loop t =
            tick ();
            let t1 = whnf_core st t in
            match reduce_nat st t1 with
            | Some v -> v
            | None -> ( match unfold_definition st t1 with Some t2 -> loop t2 | None -> t1)
          in
          let r = loop e in
          cadd st.c.whnf e r;
          r)

(* ---- inference ---- *)

and instantiate_telescope_ty st d fvars =
  ignore st;
  E.instantiate_rev d (Array.of_list (List.rev_map snd fvars))

and mk_binding st mk fvars body =
  (* fvars: most recent first *)
  ignore st;
  let ids = Array.of_list (List.rev_map fst fvars) in
  let b = E.abstract body ids in
  let n = Array.length ids in
  let r = ref b in
  for k = n - 1 downto 0 do
    let l = local_of ids.(k) in
    let ty = E.abstract l.lty (Array.sub ids 0 k) in
    r := mk ty !r
  done;
  !r

and ensure_sort st e =
  match e.node with
  | E.Sort l -> l
  | _ -> (
      match (whnf st e).node with
      | E.Sort l -> l
      | _ -> reject "type expected, got %s" (E.to_string e))

and ensure_pi st e =
  match e.node with
  | E.Pi (d, b) -> (d, b)
  | _ -> (
      match (whnf st e).node with
      | E.Pi (d, b) -> (d, b)
      | _ -> reject "function expected: %s" (E.to_string e))

and is_prop_type st ty =
  (* [ty : Prop], i.e. the sort of [ty] is zero under every valuation *)
  match (whnf st (infer_only st ty)).node with
  | E.Sort l -> Level.is_zero l
  | _ -> false

and infer_only st e = infer st ~check:false e

and infer st ~check e =
  match e.node with
  | E.BVar _ -> reject "loose bound variable"
  | E.FVar id -> (local_of id).lty
  | _ -> (
      let c = if check then st.check_cache else st.c.infer_only in
      match cfind c e with
      | Some r -> r
      | None ->
          tick ();
          let r = infer_core st ~check e in
          cadd c e r;
          (* a full check also answers the cheap question *)
          if check then cadd st.c.infer_only e r;
          r)

and infer_core st ~check e =
  match e.node with
  | E.BVar _ | E.FVar _ -> assert false
  | E.Sort l ->
      if check && not (Level.params_within st.lparams l) then
        reject "universe parameter out of scope in %s" (Level.to_string l);
      E.sort (Level.succ l)
  | E.Nat _ ->
      if not (nat_ok st) then
        reject "natural number literal: the environment's Nat is not the genuine one";
      nat_type
  | E.Str _ ->
      if check && find_decl st n_string = None then reject "String literal without String";
      mk_const n_string
  | E.Const (n, ls) -> (
      match find_decl st n with
      | None -> reject "unknown constant %s" (Name.to_string n)
      | Some d ->
          if List.length ls <> List.length d.lparams then
            reject "wrong number of universe levels for %s" (Name.to_string n);
          if (match d.kind with Decl.Unsafe_const -> true | _ -> false) && not st.allow_unsafe
          then
            reject "%s is unsafe or partial and cannot be used by a safe declaration"
              (Name.to_string n);
          if check then
            List.iter
              (fun l ->
                if not (Level.params_within st.lparams l) then
                  reject "universe parameter out of scope in %s" (Name.to_string n))
              ls;
          E.inst_lparams d.lparams ls d.ty)
  | E.App _ ->
      let f = E.get_app_fn e and args = E.get_app_args e in
      let ft = ref (infer st ~check f) in
      List.iter
        (fun a ->
          let d, b = ensure_pi st !ft in
          if check then begin
            let at = infer st ~check:true a in
            if not (is_def_eq st at d) then
              reject "application type mismatch: argument %s has type %s, expected %s"
                (E.to_string a) (E.to_string at) (E.to_string d)
          end;
          ft := E.instantiate1 b a)
        args;
      !ft
  | E.Lam _ ->
      let rec go e fvars =
        match e.node with
        | E.Lam (d, b) ->
            let d' = instantiate_telescope_ty st d fvars in
            if check then ignore (ensure_sort st (infer st ~check:true d'));
            let fv = fresh_fvar d' in
            go b (fv :: fvars)
        | _ ->
            let body = instantiate_telescope_ty st e fvars in
            let r = infer st ~check body in
            let result = mk_binding st E.pi fvars r in
            drop_locals st (List.map fst fvars);
            result
      in
      go e []
  | E.Pi _ ->
      let rec go e fvars levels =
        match e.node with
        | E.Pi (d, b) ->
            let d' = instantiate_telescope_ty st d fvars in
            let l = ensure_sort st (infer st ~check d') in
            let fv = fresh_fvar d' in
            go b (fv :: fvars) (l :: levels)
        | _ ->
            let body = instantiate_telescope_ty st e fvars in
            let l = ensure_sort st (infer st ~check body) in
            drop_locals st (List.map fst fvars);
            E.sort (List.fold_left (fun acc li -> Level.imax li acc) l levels)
      in
      go e [] []
  | E.Let (t, v, b) ->
      if check then begin
        ignore (ensure_sort st (infer st ~check:true t));
        let vt = infer st ~check:true v in
        if not (is_def_eq st vt t) then reject "let value has the wrong type"
      end;
      let id, fv = fresh_fvar ~value:v t in
      let r = infer st ~check (E.instantiate1 b fv) in
      let result = E.instantiate1 (E.abstract r [| id |]) v in
      drop_locals st [ id ];
      result
  | E.Proj (sname, idx, s) -> infer_proj st ~check sname idx s

and infer_proj st ~check sname idx s =
  let raw_ty = infer st ~check s in
  let st_ty = whnf st raw_ty in
  match (E.get_app_fn st_ty).node with
  | E.Const (i, ls) when i == sname -> (
      match induct_of st i with
      | Some { ctors = [ c ]; nparams; nindices = 0; _ } -> (
          let args = E.get_app_args st_ty in
          if List.length args <> nparams then reject "projection: wrong number of parameters";
          match find_decl st c with
          | Some ({ kind = Decl.Ctor ci; _ } as cd) ->
              if idx >= ci.nfields then reject "projection index out of range";
              (* the structure is a proposition if either presentation of its type is one: the type as inferred, or its
                 normal form (a type that is a proposition by declaration can normalise to something whose sort is
                 stuck) *)
              let is_prop = is_prop_type st raw_ty || is_prop_type st st_ty in
              let ct = ref (E.inst_lparams cd.lparams ls cd.ty) in
              List.iter
                (fun a ->
                  let _, b = ensure_pi st !ct in
                  ct := E.instantiate1 b a)
                args;
              for k = 0 to idx - 1 do
                let d, b = ensure_pi st !ct in
                if E.has_loose_bvar b 0 then begin
                  if is_prop && not (is_prop_type st d) then
                    reject "projection of a proof into a non-proposition";
                  ct := E.instantiate1 b (E.proj i k s)
                end
                else ct := E.instantiate1 b s
              done;
              let d, _ = ensure_pi st !ct in
              if is_prop && not (is_prop_type st d) then
                reject "projection of a proof into a non-proposition";
              d
          | _ -> reject "projection: not a structure")
      | _ -> reject "projection: not a structure")
  | _ -> reject "projection: the structure's type is not %s" (Name.to_string sname)

(* ---- definitional equality ---- *)

and is_def_eq st a b =
  tick ();
  if a == b then true
  else
    let key = if a.id <= b.id then (a.id, b.id) else (b.id, a.id) in
    if Hashtbl.mem st.c.eq_ok key then true
    else if Hashtbl.mem st.c.eq_fail key then false
    else begin
      let r = is_def_eq_core st a b in
      if (not r) && trace then begin
        let t e =
          let s = E.to_string e in
          if String.length s > 400 then String.sub s 0 400 ^ "…" else s
        in
        Printf.eprintf "NOT DEFEQ:\n  %s\n  %s\n%!" (t a) (t b)
      end;
      (* terms with free variables stand for open goals in the current telescope; only cache closed answers *)
      if not (a.has_fvar || b.has_fvar) then
        Hashtbl.replace (if r then st.c.eq_ok else st.c.eq_fail) key ();
      r
    end

and quick_is_def_eq st a b =
  if a == b then `True
  else
    match (a.node, b.node) with
    | E.Lam _, E.Lam _ | E.Pi _, E.Pi _ -> if is_def_eq_binding st a b then `True else `False
    | E.Sort l1, E.Sort l2 -> if Level.equiv l1 l2 then `True else `False
    | E.Nat x, E.Nat y -> if Z.equal x y then `True else `False
    | E.Str x, E.Str y -> if String.equal x y then `True else `False
    | _ -> `Unknown

and is_def_eq_binding st a b =
  let rec go a b fvars =
    match (a.E.node, b.E.node) with
    | E.Lam (d1, b1), E.Lam (d2, b2) | E.Pi (d1, b1), E.Pi (d2, b2) ->
        let d1' = instantiate_telescope_ty st d1 fvars in
        let d2' = instantiate_telescope_ty st d2 fvars in
        if d1' != d2' && not (is_def_eq st d1' d2') then false
        else
          let fv = fresh_fvar d1' in
          go b1 b2 (fv :: fvars)
    | _ ->
        let r =
          is_def_eq st (instantiate_telescope_ty st a fvars) (instantiate_telescope_ty st b fvars)
        in
        drop_locals st (List.map fst fvars);
        r
  in
  go a b []

and is_def_eq_args st a b =
  let rec go a b =
    match (a.E.node, b.E.node) with
    | E.App (f1, x1), E.App (f2, x2) -> is_def_eq st x1 x2 && go f1 f2
    | E.App _, _ | _, E.App _ -> false
    | _ -> true
  in
  go a b

and is_def_eq_levels l1 l2 = List.length l1 = List.length l2 && List.for_all2 Level.equiv l1 l2

and is_def_eq_proof_irrel st t s =
  let tt = infer_only st t in
  if not (is_prop_type st tt) then `Unknown
  else
    let ts = infer_only st s in
    if is_def_eq st tt ts then `True else `False

and nat_succ_pred st e =
  if not (nat_ok st) then None
  else
    match e.node with
    | E.Nat z when Z.gt z Z.zero -> Some (E.nat (Z.pred z))
    | E.App (f, a) when is_const_named f n_nat_succ -> Some a
    | _ -> None

and is_def_eq_offset_nat st t s =
  match (nat_lit_ext st t, nat_lit_ext st s) with
  | Some x, Some y -> if Z.equal x y then `True else `False
  | _ -> (
      match (nat_succ_pred st t, nat_succ_pred st s) with
      | Some pt, Some ps -> if is_def_eq st pt ps then `True else `False
      | _ -> `Unknown)

and try_eta_expansion st t s = try_eta_expansion_core st t s || try_eta_expansion_core st s t

and try_eta_expansion_core st t s =
  match (t.node, s.node) with
  | E.Lam _, E.Lam _ -> false
  | E.Lam _, _ -> (
      let s_ty = whnf st (infer_only st s) in
      match s_ty.node with
      | E.Pi (d, _) -> is_def_eq st t (E.lam d (E.app s (E.bvar 0)))
      | _ -> false)
  | _ -> false

and try_eta_struct st t s = try_eta_struct_core st t s || try_eta_struct_core st s t

and try_eta_struct_core st t s =
  match (E.get_app_fn s).node with
  | E.Const (c, _) -> (
      match ctor_of st c with
      | Some ci ->
          let args = E.get_app_args s in
          if List.length args <> ci.cparams + ci.nfields then false
          else if not (is_structure_like st ci.induct) then false
          else if not (is_def_eq st (infer_only st t) (infer_only st s)) then false
          else
            List.for_all Fun.id
              (List.mapi
                 (fun i a -> i < ci.cparams || is_def_eq st (E.proj ci.induct (i - ci.cparams) t) a)
                 args)
      | None -> false)
  | _ -> false

and is_def_eq_unit_like st t s =
  let t_ty = whnf st (infer_only st t) in
  match (E.get_app_fn t_ty).node with
  | E.Const (i, _) when is_structure_like st i -> (
      match induct_of st i with
      | Some { ctors = [ c ]; _ } -> (
          match ctor_of st c with
          | Some { nfields = 0; _ } -> is_def_eq st t_ty (infer_only st s)
          | _ -> false)
      | _ -> false)
  | _ -> false

and try_string_lit_expansion st t s =
  match (t.node, s.node) with
  | E.Str str, E.App _ when is_string_ctor (E.get_app_fn s) ->
      `Res (is_def_eq_core st (string_lit_to_ctor st str) s)
  | E.App _, E.Str str when is_string_ctor (E.get_app_fn t) ->
      `Res (is_def_eq_core st t (string_lit_to_ctor st str))
  | _ -> `Unknown

and compare_hints (h1 : Decl.hints) (h2 : Decl.hints) =
  match (h1, h2) with
  | Decl.Regular a, Decl.Regular b -> if a = b then 0 else if a > b then -1 else 1
  | Decl.Opaque, Decl.Opaque | Decl.Abbrev, Decl.Abbrev -> 0
  | Decl.Opaque, _ -> 1
  | _, Decl.Opaque -> -1
  | Decl.Abbrev, _ -> -1
  | _, Decl.Abbrev -> 1

and lazy_delta_step st tn sn =
  match is_def_eq_offset_nat st tn sn with
  | `True -> `Done true
  | `False -> `Done false
  | `Unknown -> (
      (* The kernel tries this only when neither side has a free variable. Here a let-bound variable whose value is closed
         counts as closed: [Nat.beq lit (e[x := let-bound])] would otherwise be compared by peeling the literal one
         successor at a time. A term with any other free variable is left alone, as in the kernel: reducing its
         arguments can force an arithmetic expression over a variable that will never become a literal. *)
      let nat_step =
        if closed_modulo_lets tn && closed_modulo_lets sn then
          match reduce_nat st tn with
          | Some t' -> Some (`Done (is_def_eq_core st t' sn))
          | None -> (
              match reduce_nat st sn with
              | Some s' -> Some (`Done (is_def_eq_core st tn s'))
              | None -> None)
        else None
      in
      match nat_step with
      | Some r -> r
      | None -> (
          let dt = unfoldable st tn and ds = unfoldable st sn in
          let unfold x =
            match unfold_definition st x with
            | Some u -> whnf_core ~cheap_proj:true st u
            | None -> x
          in
          let step =
            (* The kernel's rule (try_unfold_proj_app): when only one side can be unfolded and the other is a projection
               application that whnf_core can reduce, reduce that one instead. Otherwise [expensive =?= inst.1 a] keeps
               unfolding [expensive] (a function defined by well-founded or large structural recursion) when the
               projection would have exposed a term to compare it with. *)
            let proj_app_step e =
              match (E.get_app_fn e).node with
              | E.Proj _ ->
                  let e' = whnf_core st e in
                  if e' != e then Some e' else None
              | _ -> None
            in
            match (dt, ds) with
            | None, None -> `Stuck
            | Some _, None -> (
                match proj_app_step sn with
                | Some sn' -> `Next (tn, sn')
                | None -> `Next (unfold tn, sn))
            | None, Some _ -> (
                match proj_app_step tn with
                | Some tn' -> `Next (tn', sn)
                | None -> `Next (tn, unfold sn))
            | Some d1, Some d2 ->
                let c = compare_hints (hints_of d1) (hints_of d2) in
                if c < 0 then `Next (unfold tn, sn)
                else if c > 0 then `Next (tn, unfold sn)
                else begin
                  let same_args_ok =
                    match (tn.node, sn.node) with
                    | E.App _, E.App _ when d1 == d2 || Name.equal d1.name d2.name -> (
                        match hints_of d1 with
                        | Decl.Regular _ ->
                            let key = if tn.id <= sn.id then (tn.id, sn.id) else (sn.id, tn.id) in
                            if Hashtbl.mem st.c.eq_fail key then false
                            else begin
                              let ls1 =
                                match (E.get_app_fn tn).node with E.Const (_, l) -> l | _ -> []
                              in
                              let ls2 =
                                match (E.get_app_fn sn).node with E.Const (_, l) -> l | _ -> []
                              in
                              if is_def_eq_levels ls1 ls2 && is_def_eq_args st tn sn then true
                              else begin
                                if not (tn.has_fvar || sn.has_fvar) then
                                  Hashtbl.replace st.c.eq_fail key ();
                                false
                              end
                            end
                        | _ -> false)
                    | _ -> false
                  in
                  if same_args_ok then `Equal else `Next (unfold tn, unfold sn)
                end
          in
          match step with
          | `Stuck -> `Stuck
          | `Equal -> `Done true
          | `Next (tn', sn') -> (
              match quick_is_def_eq st tn' sn' with
              | `True -> `Done true
              | `False -> `Done false
              | `Unknown -> `Next (tn', sn'))))

and lazy_delta st tn sn =
  match lazy_delta_step st tn sn with
  | `Done b -> `Done b
  | `Stuck -> `Cont (tn, sn)
  | `Next (a, b) -> lazy_delta st a b

(* Two projections of the same field: unfold the structures lazily, side by side, and project as soon as neither can
   be unfolded further. Comparing the structures whole would evaluate fields that the projection never looks at. *)
and proj_reduce_core st e idx =
  let e' = whnf_core st e in
  match (E.get_app_fn e').node with
  | E.Const (c, _) -> (
      match ctor_of st c with
      | Some ci -> List.nth_opt (E.get_app_args e') (ci.cparams + idx)
      | None -> None)
  | _ -> None

and lazy_delta_proj st tc sc idx =
  match lazy_delta_step st tc sc with
  | `Done true -> true
  | `Next (a, b) -> lazy_delta_proj st a b idx
  | `Done false | `Stuck -> (
      match (proj_reduce_core st tc idx, proj_reduce_core st sc idx) with
      | Some t, Some s -> is_def_eq_core st t s
      | _ -> is_def_eq_core st tc sc)

and is_def_eq_core st t s =
  match quick_is_def_eq st t s with
  | `True -> true
  | `False -> false
  | `Unknown -> (
      let bool_true_shortcut =
        (not t.has_fvar) && is_const_named s n_bool_true && is_const_named (whnf st t) n_bool_true
      in
      if bool_true_shortcut then true
      else
        let tn = whnf_core ~cheap_proj:true st t and sn = whnf_core ~cheap_proj:true st s in
        let early =
          if tn != t || sn != s then
            match quick_is_def_eq st tn sn with
            | `True -> Some true
            | `False -> Some false
            | `Unknown -> None
          else None
        in
        match early with
        | Some r -> r
        | None -> (
            match is_def_eq_proof_irrel st tn sn with
            | `True -> true
            | `False -> false
            | `Unknown -> (
                match lazy_delta st tn sn with
                | `Done r -> r
                | `Cont (tn, sn) -> after_delta st tn sn)))

and after_delta st tn sn =
  let same_const =
    match (tn.node, sn.node) with
    | E.Const (a, l1), E.Const (b, l2) -> a == b && is_def_eq_levels l1 l2
    | _ -> false
  in
  if same_const then true
  else
    match (tn.node, sn.node) with
    | E.FVar a, E.FVar b when a = b -> true
    | E.Proj (_, i, x), E.Proj (_, j, y) when i = j && lazy_delta_proj st x y i -> true
    | _ -> (
        let tnn = whnf_core st tn and snn = whnf_core st sn in
        if tnn != tn || snn != sn then is_def_eq_core st tnn snn
        else if is_def_eq_app st tn sn then true
        else if try_eta_expansion st tn sn then true
        else if try_eta_struct st tn sn then true
        else
          match try_string_lit_expansion st tn sn with
          | `Res r -> r
          | `Unknown -> is_def_eq_unit_like st tn sn)

and is_def_eq_app st t s =
  match (t.node, s.node) with
  | E.App _, E.App _ ->
      let f1 = E.get_app_fn t and f2 = E.get_app_fn s in
      E.get_app_num_args t = E.get_app_num_args s && is_def_eq st f1 f2 && is_def_eq_args st t s
  | _ -> false

(* ---- public: evidence ---- *)

let closed (e : E.t) = if e.lbr <> 0 || e.has_fvar then reject "term is not closed"

let check_typing st e =
  if st.allow_unsafe then reject "internal: a value is never checked under the unsafe allowance";
  closed e;
  let ty = infer st ~check:true e in
  Evidence.Mint.typing ~env:(Env.id st.env) ~lparams:st.lparams e ty

let check_type st e =
  closed e;
  let ty = infer st ~check:true e in
  match (whnf st ty).node with
  | E.Sort l ->
      Evidence.Mint.is_type ~env:(Env.id st.env) ~lparams:st.lparams ~safe:(not st.allow_unsafe) e l
  | _ -> reject "type expected"

let check_conv st (a : Evidence.Typing.t) b =
  if st.allow_unsafe then
    reject "internal: a conversion is never checked under the unsafe allowance";
  if a.env <> Env.id st.env then reject "evidence from another environment";
  if is_def_eq st a.ty b then
    Some (Evidence.Mint.conv ~env:(Env.id st.env) ~lparams:st.lparams a.ty b)
  else None

let check_prop st (t : Evidence.Is_type.t) =
  if st.allow_unsafe || not t.safe then
    reject "internal: a proposition is never decided under the unsafe allowance";
  if t.env <> Env.id st.env then reject "evidence from another environment";
  if Level.is_zero t.level then
    Some (Evidence.Mint.is_prop ~env:(Env.id st.env) ~lparams:st.lparams t.e)
  else None

(* between declarations: no free variable survives, so neither does anything cached about one *)
let cache_limit = Knobs.limit "WARRANT_CACHE_LIMIT" 3_000_000

let end_decl () =
  Hashtbl.reset lctx;
  Hashtbl.iter
    (fun _ c ->
      Hashtbl.reset c.infer_only.local;
      Hashtbl.reset c.whnf_core.local;
      Hashtbl.reset c.whnf.local;
      (* caches only save work: when they grow past the limit they are emptied, never trusted to stay *)
      let size =
        Hashtbl.length c.infer_only.global
        + Hashtbl.length c.whnf_core.global + Hashtbl.length c.whnf.global + Hashtbl.length c.eq_ok
        + Hashtbl.length c.eq_fail
      in
      if size > cache_limit then begin
        Hashtbl.reset c.infer_only.global;
        Hashtbl.reset c.whnf_core.global;
        Hashtbl.reset c.whnf.global;
        Hashtbl.reset c.eq_ok;
        Hashtbl.reset c.eq_fail
      end)
    cache_tbl;
  if Hashtbl.length Fingerprint.memo > 1_000_000 then Hashtbl.reset Fingerprint.memo

let run_with_fuel f =
  fuel := default_fuel;
  f ()
