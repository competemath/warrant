type t = { id : int; node : node; lbr : int; has_fvar : bool; maxfv : int; has_lparam : bool }

and node =
  | BVar of int
  | FVar of int
  | Sort of Level.t
  | Const of Name.t * Level.t list
  | App of t * t
  | Lam of t * t
  | Pi of t * t
  | Let of t * t * t
  | Nat of Z.t
  | Str of string
  | Proj of Name.t * int * t

(* Hash-consing through a weak set: a term nobody refers to any more is collectable (the type checker builds
   quadratically many instantiated copies of large bodies, and none of them may be kept alive by the table). Caches are
   keyed by [id], and ids are never reused. *)
let rec list_phys_equal a b =
  match (a, b) with
  | [], [] -> true
  | x :: xs, y :: ys -> x == y && list_phys_equal xs ys
  | _ -> false

let shallow_equal a b =
  match (a.node, b.node) with
  | BVar i, BVar j -> i = j
  | FVar i, FVar j -> i = j
  | Sort l1, Sort l2 -> l1 == l2
  | Const (n1, l1), Const (n2, l2) -> n1 == n2 && list_phys_equal l1 l2
  | App (f1, a1), App (f2, a2) -> f1 == f2 && a1 == a2
  | Lam (d1, b1), Lam (d2, b2) | Pi (d1, b1), Pi (d2, b2) -> d1 == d2 && b1 == b2
  | Let (t1, v1, b1), Let (t2, v2, b2) -> t1 == t2 && v1 == v2 && b1 == b2
  | Proj (n1, i1, s1), Proj (n2, i2, s2) -> n1 == n2 && i1 = i2 && s1 == s2
  | _ -> false

let shallow_hash a =
  match a.node with
  | BVar i -> Hashtbl.hash (0, i)
  | FVar i -> Hashtbl.hash (1, i)
  | Sort l -> Hashtbl.hash (2, l.Level.id)
  | Const (n, ls) -> Hashtbl.hash (3, n.Name.id, List.map (fun (l : Level.t) -> l.id) ls)
  | App (f, x) -> Hashtbl.hash (4, f.id, x.id)
  | Lam (d, b) -> Hashtbl.hash (5, d.id, b.id)
  | Pi (d, b) -> Hashtbl.hash (6, d.id, b.id)
  | Let (t, v, b) -> Hashtbl.hash (7, t.id, v.id, b.id)
  | Proj (n, i, s) -> Hashtbl.hash (8, n.Name.id, i, s.id)
  | Nat _ | Str _ -> 0

module W = Weak.Make (struct
  type nonrec t = t

  let equal = shallow_equal
  let hash = shallow_hash
end)

module S = Hashtbl.Make (struct
  type nonrec t = t

  let equal = shallow_equal
  let hash = shallow_hash
end)

(* Terms the file states live for the whole run and are interned strongly; terms the checker builds on the way
   (instantiated bodies, derived types) are interned weakly, so the ones nobody refers to any more are collectable. A
   huge weak table makes every major collection clean it, so the permanent terms are kept out of it. Either way a term
   has one representative: lookups go through both. *)
let strong : t S.t = S.create 100_003
let permanent = ref false

let permanently f =
  let saved = !permanent in
  permanent := true;
  Fun.protect ~finally:(fun () -> permanent := saved) f

let tbl : W.t = W.create 100_003
let counter = ref 0

module ZH = Hashtbl.Make (struct
  type t = Z.t

  let equal = Z.equal
  let hash = Z.hash
end)

let nat_tbl : t ZH.t = ZH.create 64
let str_tbl : (string, t) Hashtbl.t = Hashtbl.create 64

let next_id () =
  let i = !counter in
  incr counter;
  i

let mk node lbr maxfv has_lparam =
  let cand = { id = next_id (); node; lbr; has_fvar = maxfv > 0; maxfv; has_lparam } in
  match S.find_opt strong cand with
  | Some e -> e
  | None ->
      if !permanent then (
        let e = match W.find_opt tbl cand with Some e -> e | None -> cand in
        S.add strong e e;
        e)
      else W.merge tbl cand

let bvar i = mk (BVar i) (i + 1) 0 false
let fvar i = mk (FVar i) 0 i false

let level_has_param l =
  let rec go (l : Level.t) =
    match l.node with
    | Zero -> false
    | Param _ -> true
    | Succ a -> go a
    | Max (a, b) | IMax (a, b) -> go a || go b
  in
  go l

let sort l = mk (Sort l) 0 0 (level_has_param l)
let const n ls = mk (Const (n, ls)) 0 0 (List.exists level_has_param ls)
let app f a = mk (App (f, a)) (max f.lbr a.lbr) (max f.maxfv a.maxfv) (f.has_lparam || a.has_lparam)

let binder mkn d b =
  mk (mkn d b) (max d.lbr (max 0 (b.lbr - 1))) (max d.maxfv b.maxfv) (d.has_lparam || b.has_lparam)

let lam d b = binder (fun d b -> Lam (d, b)) d b
let pi d b = binder (fun d b -> Pi (d, b)) d b

let let_ t v b =
  mk
    (Let (t, v, b))
    (max t.lbr (max v.lbr (max 0 (b.lbr - 1))))
    (max t.maxfv (max v.maxfv b.maxfv))
    (t.has_lparam || v.has_lparam || b.has_lparam)

let nat z =
  match ZH.find_opt nat_tbl z with
  | Some e -> e
  | None ->
      let e =
        { id = next_id (); node = Nat z; lbr = 0; has_fvar = false; maxfv = 0; has_lparam = false }
      in
      ZH.add nat_tbl z e;
      e

let str s =
  match Hashtbl.find_opt str_tbl s with
  | Some e -> e
  | None ->
      let e =
        { id = next_id (); node = Str s; lbr = 0; has_fvar = false; maxfv = 0; has_lparam = false }
      in
      Hashtbl.add str_tbl s e;
      e

let proj n i e = mk (Proj (n, i, e)) e.lbr e.maxfv e.has_lparam
let mk_app f args = List.fold_left app f args
let rec get_app_fn e = match e.node with App (f, _) -> get_app_fn f | _ -> e

let get_app_args e =
  let rec go e acc = match e.node with App (f, a) -> go f (a :: acc) | _ -> acc in
  go e []

let rec get_app_num_args e = match e.node with App (f, _) -> 1 + get_app_num_args f | _ -> 0

(* Rebuild a term bottom-up. [f offset e] may answer for a whole subterm; otherwise the children are visited. *)
let replace (f : int -> t -> t option) (e : t) : t =
  let memo : (int * int, t) Hashtbl.t Lazy.t = lazy (Hashtbl.create 16) in
  let memo_used = ref false in
  let rec go off e =
    match f off e with
    | Some r -> r
    | None -> (
        let key = (e.id, off) in
        match if !memo_used then Hashtbl.find_opt (Lazy.force memo) key else None with
        | Some r -> r
        | None ->
            let r =
              match e.node with
              | App (a, b) -> app (go off a) (go off b)
              | Lam (d, b) -> lam (go off d) (go (off + 1) b)
              | Pi (d, b) -> pi (go off d) (go (off + 1) b)
              | Let (t, v, b) -> let_ (go off t) (go off v) (go (off + 1) b)
              | Proj (n, i, s) -> proj n i (go off s)
              | BVar _ | FVar _ | Sort _ | Const _ | Nat _ | Str _ -> e
            in
            memo_used := true;
            Hashtbl.add (Lazy.force memo) key r;
            r)
  in
  go 0 e

let lift_loose e n k =
  (* lift loose bvars >= n by k *)
  if k = 0 || e.lbr <= n then e
  else
    replace
      (fun off e ->
        if e.lbr <= n + off then Some e
        else match e.node with BVar i -> Some (bvar (i + k)) | _ -> None)
      e

let instantiate_rev e subst =
  let n = Array.length subst in
  if n = 0 || e.lbr = 0 then e
  else
    replace
      (fun off e ->
        if e.lbr <= off then Some e
        else
          match e.node with
          | BVar i ->
              if i < off then Some e
              else if i - off < n then
                let s = subst.(n - 1 - (i - off)) in
                Some (lift_loose s 0 off)
              else Some (bvar (i - n))
          | _ -> None)
      e

let instantiate1 e a = instantiate_rev e [| a |]

let abstract e ids =
  let n = Array.length ids in
  if n = 0 || not e.has_fvar then e
  else
    let index = Hashtbl.create 8 in
    Array.iteri (fun k id -> Hashtbl.replace index id k) ids;
    replace
      (fun off e ->
        if not e.has_fvar then Some e
        else
          match e.node with
          | FVar id -> (
              match Hashtbl.find_opt index id with
              | Some k -> Some (bvar (n - 1 - k + off))
              | None -> Some e)
          | _ -> None)
      e

let inst_lparams ps ls e =
  if ps = [] || not e.has_lparam then e
  else
    replace
      (fun _ e ->
        if not e.has_lparam then Some e
        else
          match e.node with
          | Sort l -> Some (sort (Level.inst ps ls l))
          | Const (n, us) -> Some (const n (List.map (Level.inst ps ls) us))
          | _ -> None)
      e

let has_loose_bvar e i =
  let seen = Hashtbl.create 16 in
  let rec go off e =
    if e.lbr <= i + off then false
    else
      let key = (e.id, off) in
      if Hashtbl.mem seen key then false
      else begin
        Hashtbl.add seen key ();
        match e.node with
        | BVar j -> j = i + off
        | App (a, b) -> go off a || go off b
        | Lam (d, b) | Pi (d, b) -> go off d || go (off + 1) b
        | Let (t, v, b) -> go off t || go off v || go (off + 1) b
        | Proj (_, _, s) -> go off s
        | FVar _ | Sort _ | Const _ | Nat _ | Str _ -> false
      end
  in
  go 0 e

let consts e =
  let seen = Hashtbl.create 16 and acc = ref [] in
  let rec go e =
    if not (Hashtbl.mem seen e.id) then begin
      Hashtbl.add seen e.id ();
      match e.node with
      | Const (n, _) -> if not (List.memq n !acc) then acc := n :: !acc
      | App (a, b) | Lam (a, b) | Pi (a, b) ->
          go a;
          go b
      | Let (t, v, b) ->
          go t;
          go v;
          go b
      | Proj (n, _, s) ->
          if not (List.memq n !acc) then acc := n :: !acc;
          go s
      | BVar _ | FVar _ | Sort _ | Nat _ | Str _ -> ()
    end
  in
  go e;
  List.rev !acc

(* [for_all_fvars p e]: every free variable of [e] satisfies [p]. Only subterms with free variables are visited. *)
let for_all_fvars p e =
  let seen = Hashtbl.create 16 in
  let rec go e =
    if not e.has_fvar then true
    else if Hashtbl.mem seen e.id then true
    else begin
      Hashtbl.add seen e.id ();
      match e.node with
      | FVar i -> p i
      | App (a, b) | Lam (a, b) | Pi (a, b) -> go a && go b
      | Let (t, v, b) -> go t && go v && go b
      | Proj (_, _, s) -> go s
      | BVar _ | Sort _ | Const _ | Nat _ | Str _ -> true
    end
  in
  go e

let exists_const p e =
  let seen = Hashtbl.create 16 in
  let rec go e =
    if Hashtbl.mem seen e.id then false
    else begin
      Hashtbl.add seen e.id ();
      match e.node with
      | Const (n, _) -> p n
      | App (a, b) | Lam (a, b) | Pi (a, b) -> go a || go b
      | Let (t, v, b) -> go t || go v || go b
      | Proj (_, _, s) -> go s
      | BVar _ | FVar _ | Sort _ | Nat _ | Str _ -> false
    end
  in
  go e

let rec to_string e =
  match e.node with
  | BVar i -> "#" ^ string_of_int i
  | FVar i -> "@" ^ string_of_int i
  | Sort l -> "Sort " ^ Level.to_string l
  | Const (n, ls) ->
      Name.to_string n
      ^ if ls = [] then "" else ".{" ^ String.concat "," (List.map Level.to_string ls) ^ "}"
  | App (f, a) -> "(" ^ to_string f ^ " " ^ to_string a ^ ")"
  | Lam (d, b) -> "(fun " ^ to_string d ^ " => " ^ to_string b ^ ")"
  | Pi (d, b) -> "(" ^ to_string d ^ " -> " ^ to_string b ^ ")"
  | Let (t, v, b) -> "(let " ^ to_string t ^ " := " ^ to_string v ^ "; " ^ to_string b ^ ")"
  | Nat z -> Z.to_string z
  | Str s -> Printf.sprintf "%S" s
  | Proj (n, i, s) -> to_string s ^ "." ^ Name.to_string n ^ "#" ^ string_of_int i
