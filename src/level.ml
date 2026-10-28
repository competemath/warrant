type t = { id : int; node : node }
and node = Zero | Succ of t | Max of t * t | IMax of t * t | Param of Name.t

let tbl : (int * int * int, t) Hashtbl.t = Hashtbl.create 4096
let counter = ref 0

let mk key node =
  match Hashtbl.find_opt tbl key with
  | Some l -> l
  | None ->
      let l = { id = !counter; node } in
      incr counter;
      Hashtbl.add tbl key l;
      l

let zero = mk (0, 0, 0) Zero
let succ a = mk (1, a.id, 0) (Succ a)
let max a b = mk (2, a.id, b.id) (Max (a, b))
let imax a b = mk (3, a.id, b.id) (IMax (a, b))
let param n = mk (4, n.Name.id, 0) (Param n)
let one = succ zero
let equal (a : t) (b : t) = a == b
let hash a = a.id

let rec to_string l =
  match l.node with
  | Zero -> "0"
  | Succ a -> "(succ " ^ to_string a ^ ")"
  | Max (a, b) -> "(max " ^ to_string a ^ " " ^ to_string b ^ ")"
  | IMax (a, b) -> "(imax " ^ to_string a ^ " " ^ to_string b ^ ")"
  | Param n -> Name.to_string n

let inst ps ls l =
  if ps = [] then l
  else
    let memo = Hashtbl.create 16 in
    let rec go l =
      match l.node with
      | Zero -> l
      | Param n ->
          let rec find ps ls =
            match (ps, ls) with p :: ps, v :: ls -> if p == n then v else find ps ls | _ -> l
          in
          find ps ls
      | Succ a -> (
          match Hashtbl.find_opt memo l.id with
          | Some r -> r
          | None ->
              let r = succ (go a) in
              Hashtbl.add memo l.id r;
              r)
      | Max (a, b) | IMax (a, b) -> (
          match Hashtbl.find_opt memo l.id with
          | Some r -> r
          | None ->
              let a' = go a and b' = go b in
              let r = match l.node with Max _ -> max a' b' | _ -> imax a' b' in
              Hashtbl.add memo l.id r;
              r)
    in
    go l

let rec params_within ps l =
  match l.node with
  | Zero -> true
  | Param n -> List.memq n ps
  | Succ a -> params_within ps a
  | Max (a, b) | IMax (a, b) -> params_within ps a && params_within ps b

exception Too_complex

let add_uniq x acc = if List.memq x acc then acc else x :: acc

let rec all_params l acc =
  match l.node with
  | Zero -> acc
  | Param n -> add_uniq n acc
  | Succ a -> all_params a acc
  | Max (a, b) | IMax (a, b) -> all_params b (all_params a acc)

(* the parameters whose zero-ness decides some [imax] in the level *)
let rec split_params l acc =
  match l.node with
  | Zero | Param _ -> acc
  | Succ a -> split_params a acc
  | Max (a, b) -> split_params b (split_params a acc)
  | IMax (a, b) -> split_params b (split_params a (all_params b acc))

(* replace each split parameter p by 0 (false) or by succ p (true; the parameter now stands for p - 1) *)
let rec assign sigma l =
  match l.node with
  | Zero -> l
  | Succ a -> succ (assign sigma a)
  | Max (a, b) -> max (assign sigma a) (assign sigma b)
  | IMax (a, b) -> imax (assign sigma a) (assign sigma b)
  | Param n -> (
      match List.assq_opt n sigma with Some false -> zero | Some true -> succ l | None -> l)

(* after [assign], the zero-ness of every second [imax] argument is syntactic *)
let rec nz l =
  match l.node with
  | Zero | Param _ -> false
  | Succ _ -> true
  | Max (a, b) -> nz a || nz b
  | IMax (_, b) -> nz b

(* max/succ normal form: the level is the maximum of [param + offset] terms and constants *)
let rec terms l =
  match l.node with
  | Zero -> [ (None, 0) ]
  | Succ a -> List.map (fun (x, k) -> (x, k + 1)) (terms a)
  | Max (a, b) -> terms a @ terms b
  | Param p -> [ (Some p, 0) ]
  | IMax (a, b) -> if nz b then terms a @ terms b else [ (None, 0) ]

let term_leq (x, k) ts2 =
  List.exists
    (fun (y, j) ->
      match (x, y) with
      | None, _ -> k <= j
      | Some p, Some q -> p == q && k <= j
      | Some _, None -> false)
    ts2

let max_splits = 14

let rec for_all_assignments split sigma f =
  match split with
  | [] -> f sigma
  | p :: rest ->
      for_all_assignments rest ((p, false) :: sigma) f
      && for_all_assignments rest ((p, true) :: sigma) f

type leq = { lhs : t; rhs : t }

let cache : (int * int, bool) Hashtbl.t = Hashtbl.create 1024

let decide a b =
  if a == b then true
  else
    match Hashtbl.find_opt cache (a.id, b.id) with
    | Some r -> r
    | None ->
        let split = split_params b (split_params a []) in
        if List.length split > max_splits then raise Too_complex;
        let r =
          for_all_assignments split [] (fun sigma ->
              let ts1 = terms (assign sigma a) and ts2 = terms (assign sigma b) in
              List.for_all (fun t -> term_leq t ts2) ts1)
        in
        Hashtbl.add cache (a.id, b.id) r;
        r

let leq a b = if decide a b then Some { lhs = a; rhs = b } else None
let equiv a b = a == b || (decide a b && decide b a)
let is_zero l = decide l zero
let is_never_zero l = decide one l
