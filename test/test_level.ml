(* The universe-level decision procedure against brute-force evaluation.

   [Level.leq a b] claims [a <= b] under every valuation of the parameters in the naturals. The oracle evaluates both
   levels on every valuation of the parameters over 0..bound, where [bound] exceeds every offset that occurs, so a
   counterexample (if there is one) is inside the grid: the two must agree exactly. *)

open Warrant

let ps = [| Name.of_dotted "u"; Name.of_dotted "v"; Name.of_dotted "w" |]

let rec eval (vals : int array) (l : Level.t) =
  match l.node with
  | Level.Zero -> 0
  | Level.Succ a -> 1 + eval vals a
  | Level.Max (a, b) -> max (eval vals a) (eval vals b)
  | Level.IMax (a, b) ->
      let vb = eval vals b in
      if vb = 0 then 0 else max (eval vals a) vb
  | Level.Param n ->
      let rec idx i = if ps.(i) == n then i else idx (i + 1) in
      vals.(idx 0)

let rec depth (l : Level.t) =
  match l.node with
  | Level.Zero | Level.Param _ -> 0
  | Level.Succ a -> 1 + depth a
  | Level.Max (a, b) | Level.IMax (a, b) -> 1 + max (depth a) (depth b)

let gen_level =
  let open QCheck.Gen in
  sized_size (int_range 0 5)
  @@ fix (fun self n ->
      if n = 0 then oneof [ return Level.zero; map (fun i -> Level.param ps.(i)) (int_range 0 2) ]
      else
        oneof_weighted
          [
            (1, return Level.zero);
            (2, map (fun i -> Level.param ps.(i)) (int_range 0 2));
            (2, map Level.succ (self (n - 1)));
            (2, map2 Level.max (self (n / 2)) (self (n / 2)));
            (2, map2 Level.imax (self (n / 2)) (self (n / 2)));
          ])

let arb_level = QCheck.make ~print:Level.to_string gen_level

let grid_leq a b =
  let bound = depth a + depth b + 2 in
  let ok = ref true in
  for x = 0 to bound do
    for y = 0 to bound do
      for z = 0 to bound do
        let v = [| x; y; z |] in
        if eval v a > eval v b then ok := false
      done
    done
  done;
  !ok

let prop_leq =
  QCheck.Test.make ~count:3000 ~name:"leq agrees with evaluation on a grid"
    (QCheck.pair arb_level arb_level) (fun (a, b) -> Level.leq a b <> None = grid_leq a b)

let prop_zero =
  QCheck.Test.make ~count:2000 ~name:"is_zero iff zero on the grid" arb_level (fun a ->
      Level.is_zero a = grid_leq a Level.zero)

let prop_never_zero =
  QCheck.Test.make ~count:2000 ~name:"is_never_zero iff at least one on the grid" arb_level
    (fun a -> Level.is_never_zero a = grid_leq Level.one a)

let prop_equiv_sym =
  QCheck.Test.make ~count:1500 ~name:"equiv is symmetric and agrees with the grid"
    (QCheck.pair arb_level arb_level) (fun (a, b) ->
      Level.equiv a b = Level.equiv b a && Level.equiv a b = (grid_leq a b && grid_leq b a))

let u = Level.param ps.(0)
let v = Level.param ps.(1)

(* the historical bugs in this component, as known answers *)
let known () =
  Alcotest.(check bool) "imax u 0 is zero" true (Level.is_zero (Level.imax u Level.zero));
  Alcotest.(check bool)
    "imax u (succ v) = max u (succ v)" true
    (Level.equiv (Level.imax u (Level.succ v)) (Level.max u (Level.succ v)));
  Alcotest.(check bool)
    "imax u v <= 0 is false" false
    (Level.leq (Level.imax u v) Level.zero <> None);
  Alcotest.(check bool) "0 is not never-zero" false (Level.is_never_zero Level.zero);
  Alcotest.(check bool) "succ u is never zero" true (Level.is_never_zero (Level.succ u));
  Alcotest.(check bool) "imax u v is not never-zero" false (Level.is_never_zero (Level.imax u v));
  Alcotest.(check bool)
    "imax u (succ v) is never zero" true
    (Level.is_never_zero (Level.imax u (Level.succ v)));
  Alcotest.(check bool) "max u v = max v u" true (Level.equiv (Level.max u v) (Level.max v u));
  Alcotest.(check bool) "u <= v is false" false (Level.leq u v <> None);
  Alcotest.(check bool)
    "imax (imax u v) w = imax u (imax v w)" false
    (Level.equiv
       (Level.imax (Level.imax u v) (Level.param ps.(2)))
       (Level.imax u (Level.imax v (Level.param ps.(2)))))

let () =
  Alcotest.run "level"
    [
      ("known answers", [ Alcotest.test_case "historical level bugs" `Quick known ]);
      ( "properties",
        List.map QCheck_alcotest.to_alcotest
          [ prop_leq; prop_zero; prop_never_zero; prop_equiv_sym ] );
    ]
