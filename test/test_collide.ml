(* Hash-consing under total collision: this test runs with WARRANT_HASH_MASK=0 (see test/dune), so every term has the same
   hash and whether two terms are one term is decided by the equality test alone. Two terms are physically equal exactly
   when they were built from the same description. *)

open Warrant
module E = Expr

type spec =
  | B of int
  | F of int
  | Sort of int
  | Const of int * int list
  | App of spec * spec
  | Lam of spec * spec
  | Pi of spec * spec
  | Let of spec * spec * spec
  | Proj of int * int * spec
  | Nat of int
  | Str of string

let level i =
  let rec go i = if i = 0 then Level.zero else Level.succ (go (i - 1)) in
  go i

let name i = Name.of_dotted (Printf.sprintf "n%d" i)

let rec build = function
  | B i -> E.bvar i
  | F i -> E.fvar i
  | Sort i -> E.sort (level i)
  | Const (n, ls) -> E.const (name n) (List.map level ls)
  | App (a, b) -> E.app (build a) (build b)
  | Lam (a, b) -> E.lam (build a) (build b)
  | Pi (a, b) -> E.pi (build a) (build b)
  | Let (a, b, c) -> E.let_ (build a) (build b) (build c)
  | Proj (n, i, s) -> E.proj (name n) i (build s)
  | Nat i -> E.nat (Z.of_int i)
  | Str s -> E.str s

let rec to_s = function
  | B i -> Printf.sprintf "B%d" i
  | F i -> Printf.sprintf "F%d" i
  | Sort i -> Printf.sprintf "Sort%d" i
  | Const (n, ls) -> Printf.sprintf "C%d[%s]" n (String.concat ";" (List.map string_of_int ls))
  | App (a, b) -> Printf.sprintf "(%s %s)" (to_s a) (to_s b)
  | Lam (a, b) -> Printf.sprintf "(fun %s %s)" (to_s a) (to_s b)
  | Pi (a, b) -> Printf.sprintf "(pi %s %s)" (to_s a) (to_s b)
  | Let (a, b, c) -> Printf.sprintf "(let %s %s %s)" (to_s a) (to_s b) (to_s c)
  | Proj (n, i, s) -> Printf.sprintf "(proj n%d %d %s)" n i (to_s s)
  | Nat i -> Printf.sprintf "#%d" i
  | Str s -> Printf.sprintf "%S" s

let rec gen depth =
  let open QCheck.Gen in
  let leaf =
    oneof
      [
        map (fun i -> B i) (int_range 0 2);
        map (fun i -> F i) (int_range 0 2);
        map (fun i -> Sort i) (int_range 0 2);
        map2 (fun n ls -> Const (n, ls)) (int_range 0 2) (list_size (int_range 0 2) (int_range 0 2));
        map (fun i -> Nat i) (int_range 0 2);
        map (fun s -> Str s) (oneof_list [ ""; "a"; "b" ]);
      ]
  in
  if depth = 0 then leaf
  else
    let sub = gen (depth - 1) in
    oneof_weighted
      [
        (3, leaf);
        (2, map2 (fun a b -> App (a, b)) sub sub);
        (1, map2 (fun a b -> Lam (a, b)) sub sub);
        (1, map2 (fun a b -> Pi (a, b)) sub sub);
        (1, map3 (fun a b c -> Let (a, b, c)) sub sub sub);
        (2, map3 (fun n i s -> Proj (n, i, s)) (int_range 0 2) (int_range 0 2) sub);
      ]

(* a copy of [s] with one place changed: the pairs worth comparing are the ones that differ in a single field *)
let rec change s =
  let open QCheck.Gen in
  let here = gen 1 in
  match s with
  | App (a, b) ->
      oneof [ here; map (fun a -> App (a, b)) (change a); map (fun b -> App (a, b)) (change b) ]
  | Lam (a, b) ->
      oneof
        [
          here;
          map (fun a -> Lam (a, b)) (change a);
          map (fun b -> Lam (a, b)) (change b);
          return (Pi (a, b));
        ]
  | Pi (a, b) ->
      oneof
        [
          here;
          map (fun a -> Pi (a, b)) (change a);
          map (fun b -> Pi (a, b)) (change b);
          return (Lam (a, b));
        ]
  | Let (a, b, c) ->
      oneof
        [
          here;
          map (fun a -> Let (a, b, c)) (change a);
          map (fun b -> Let (a, b, c)) (change b);
          map (fun c -> Let (a, b, c)) (change c);
        ]
  | Proj (n, i, x) ->
      oneof
        [
          here;
          map (fun n -> Proj (n, i, x)) (int_range 0 2);
          map (fun i -> Proj (n, i, x)) (int_range 0 2);
          map (fun x -> Proj (n, i, x)) (change x);
        ]
  | Const (n, ls) ->
      oneof
        [
          here;
          map (fun n -> Const (n, ls)) (int_range 0 2);
          map (fun ls -> Const (n, ls)) (list_size (int_range 0 2) (int_range 0 2));
        ]
  | _ -> here

let pair =
  let open QCheck.Gen in
  gen 3 >>= fun s -> oneof [ return (s, s); map (fun t -> (s, t)) (change s) ]

let prop_faithful =
  QCheck.Test.make ~count:2000
    ~name:"under total collision, terms are one term exactly when built the same way"
    (QCheck.make ~print:(fun (a, b) -> to_s a ^ "  vs  " ^ to_s b) pair)
    (fun (a, b) -> build a == build b = (a = b))

(* the same description built twice is one term, however much else was built in between *)
let prop_stable =
  QCheck.Test.make ~count:2000 ~name:"a term is found again"
    (QCheck.make ~print:to_s (gen 3))
    (fun s ->
      let first = build s in
      ignore (build (Lam (s, App (s, s))));
      first == build s)

let () =
  Alcotest.run "collide"
    [ ("hash-consing", List.map QCheck_alcotest.to_alcotest [ prop_faithful; prop_stable ]) ]
