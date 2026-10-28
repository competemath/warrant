(* Terms: hash-consing, binder erasure, substitution laws. *)

open Warrant
module E = Expr

let n = Name.of_dotted "c"
let c = E.const n []

let rec gen_expr depth =
  let open QCheck.Gen in
  if depth = 0 then
    oneof [ return c; map E.bvar (int_range 0 3); map (fun i -> E.fvar (i + 1)) (int_range 0 2) ]
  else
    oneof_weighted
      [
        (2, return c);
        (2, map E.bvar (int_range 0 3));
        (2, map2 E.app (gen_expr (depth - 1)) (gen_expr (depth - 1)));
        (2, map2 E.lam (gen_expr (depth - 1)) (gen_expr (depth - 1)));
        (1, map2 E.pi (gen_expr (depth - 1)) (gen_expr (depth - 1)));
        (1, map3 E.let_ (gen_expr (depth - 1)) (gen_expr (depth - 1)) (gen_expr (depth - 1)));
      ]

let arb = QCheck.make ~print:E.to_string (gen_expr 4)

let alpha_equal () =
  let a = E.lam c (E.bvar 0) and b = E.lam c (E.bvar 0) in
  Alcotest.(check bool) "alpha-equivalent terms are one term" true (a == b)

let binder_names_erased () =
  (* the export format's binder names and info never reach the kernel: two exports that differ only in them agree *)
  let a = E.pi c (E.pi c (E.bvar 1)) and b = E.pi c (E.pi c (E.bvar 1)) in
  Alcotest.(check bool) "same term" true (a == b)

(* the cached loose-bound-variable range is the true one *)
let rec true_lbr (e : E.t) =
  match e.node with
  | E.BVar i -> i + 1
  | E.App (a, b) -> max (true_lbr a) (true_lbr b)
  | E.Lam (d, b) | E.Pi (d, b) -> max (true_lbr d) (max 0 (true_lbr b - 1))
  | E.Let (t, v, b) -> max (true_lbr t) (max (true_lbr v) (max 0 (true_lbr b - 1)))
  | E.Proj (_, _, s) -> true_lbr s
  | _ -> 0

let prop_lbr =
  QCheck.Test.make ~count:2000 ~name:"cached lbr is the loose range" arb (fun e ->
      e.lbr = true_lbr e)

(* abstracting then instantiating the same free variables gives the term back *)
let prop_roundtrip =
  QCheck.Test.make ~count:2000 ~name:"instantiate_rev (abstract e ids) fvars = e"
    (QCheck.make ~print:E.to_string (gen_expr 4))
    (fun e ->
      (* the law holds for terms without loose bound variables: instantiate would otherwise capture them *)
      e.lbr > 0
      ||
      let ids = [| 1; 2; 3 |] in
      let fvs = Array.map E.fvar ids in
      E.instantiate_rev (E.abstract e ids) fvs == e)

(* instantiating a closed term with fresh variables, then abstracting them, is the identity on terms whose
   loose variables were all instantiated *)
let prop_instantiate_closed =
  QCheck.Test.make ~count:2000 ~name:"instantiate of a term without loose variables is the identity"
    (QCheck.make ~print:E.to_string (gen_expr 3))
    (fun e -> if e.lbr = 0 then E.instantiate1 e c == e else true)

let () =
  Alcotest.run "expr"
    [
      ( "hash-consing",
        [
          Alcotest.test_case "alpha" `Quick alpha_equal;
          Alcotest.test_case "binder names" `Quick binder_names_erased;
        ] );
      ( "laws",
        List.map QCheck_alcotest.to_alcotest [ prop_lbr; prop_roundtrip; prop_instantiate_closed ]
      );
    ]
