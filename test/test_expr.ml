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

(* the free variables the traversal sees are exactly the ones in the term *)
let rec true_fvars (e : E.t) =
  match e.node with
  | E.FVar i -> [ i ]
  | E.App (a, b) | E.Lam (a, b) | E.Pi (a, b) -> true_fvars a @ true_fvars b
  | E.Let (t, v, b) -> true_fvars t @ true_fvars v @ true_fvars b
  | E.Proj (_, _, s) -> true_fvars s
  | _ -> []

let prop_for_all_fvars =
  QCheck.Test.make ~count:2000 ~name:"for_all_fvars agrees with the list of free variables" arb
    (fun e ->
      let fvs = true_fvars e in
      List.for_all (fun k -> E.for_all_fvars (fun i -> i <> k) e = not (List.mem k fvs)) [ 1; 2; 3 ]
      && E.for_all_fvars (fun _ -> false) e = (fvs = []))

(* the loose-bound-variable test agrees with a plain traversal, on terms that share subterms *)
let rec true_has_loose (e : E.t) i =
  match e.node with
  | E.BVar j -> j = i
  | E.App (a, b) -> true_has_loose a i || true_has_loose b i
  | E.Lam (d, b) | E.Pi (d, b) -> true_has_loose d i || true_has_loose b (i + 1)
  | E.Let (t, v, b) -> true_has_loose t i || true_has_loose v i || true_has_loose b (i + 1)
  | E.Proj (_, _, s) -> true_has_loose s i
  | _ -> false

let gen_shared depth =
  (* the same subterm used twice, so the traversal meets a node it has already visited *)
  let open QCheck.Gen in
  map2
    (fun e k -> E.app (E.app (E.const n []) e) (if k then e else E.app e e))
    (gen_expr depth) bool

let prop_has_loose_bvar =
  QCheck.Test.make ~count:2000 ~name:"has_loose_bvar agrees with a traversal"
    (QCheck.make ~print:E.to_string (gen_shared 3))
    (fun e -> List.for_all (fun i -> E.has_loose_bvar e i = true_has_loose e i) [ 0; 1; 2; 3 ])

(* exists_const sees every constant, including inside a let *)
let rec true_consts (e : E.t) =
  match e.node with
  | E.Const (c, _) -> [ c ]
  | E.App (a, b) | E.Lam (a, b) | E.Pi (a, b) -> true_consts a @ true_consts b
  | E.Let (t, v, b) -> true_consts t @ true_consts v @ true_consts b
  | E.Proj (s, _, x) -> s :: true_consts x
  | _ -> []

let d = Name.of_dotted "d"

let prop_exists_const =
  QCheck.Test.make ~count:2000 ~name:"exists_const agrees with the list of constants"
    (QCheck.make ~print:E.to_string (gen_expr 4))
    (fun e ->
      let with_d = E.let_ (E.const d []) e c in
      E.exists_const (fun x -> x == d) with_d
      && E.exists_const (fun x -> x == n) with_d
         = List.exists (fun x -> x == n) (true_consts with_d)
      && E.exists_const (fun x -> x == n) e = List.exists (fun x -> x == n) (true_consts e))

(* instantiate_rev against a plain recursive substitution, on terms with loose variables beyond the substituted ones and
   substitutes that have loose variables of their own *)
let rec lift (e : E.t) d c =
  match e.node with
  | E.BVar i -> if i >= c then E.bvar (i + d) else e
  | E.App (a, b) -> E.app (lift a d c) (lift b d c)
  | E.Lam (a, b) -> E.lam (lift a d c) (lift b d (c + 1))
  | E.Pi (a, b) -> E.pi (lift a d c) (lift b d (c + 1))
  | E.Let (t, v, b) -> E.let_ (lift t d c) (lift v d c) (lift b d (c + 1))
  | E.Proj (s, i, x) -> E.proj s i (lift x d c)
  | _ -> e

let rec ref_inst (e : E.t) off (subst : E.t array) : E.t =
  let n = Array.length subst in
  match e.node with
  | E.BVar i ->
      if i < off then e
      else if i - off < n then lift subst.(n - 1 - (i - off)) off 0
      else E.bvar (i - n)
  | E.App (a, b) -> E.app (ref_inst a off subst) (ref_inst b off subst)
  | E.Lam (a, b) -> E.lam (ref_inst a off subst) (ref_inst b (off + 1) subst)
  | E.Pi (a, b) -> E.pi (ref_inst a off subst) (ref_inst b (off + 1) subst)
  | E.Let (t, v, b) ->
      E.let_ (ref_inst t off subst) (ref_inst v off subst) (ref_inst b (off + 1) subst)
  | E.Proj (s, i, x) -> E.proj s i (ref_inst x off subst)
  | _ -> e

let prop_instantiate_rev =
  let open QCheck.Gen in
  QCheck.Test.make ~count:3000 ~name:"instantiate_rev agrees with a plain substitution"
    (QCheck.make
       ~print:(fun (e, l) ->
         E.to_string e ^ " [" ^ String.concat "; " (List.map E.to_string l) ^ "]")
       (pair (gen_expr 4) (list_size (int_range 1 3) (gen_expr 1))))
    (fun (e, l) ->
      let subst = Array.of_list l in
      E.instantiate_rev e subst == ref_inst e 0 subst)

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
        List.map QCheck_alcotest.to_alcotest
          [
            prop_lbr;
            prop_roundtrip;
            prop_instantiate_closed;
            prop_for_all_fvars;
            prop_has_loose_bvar;
            prop_exists_const;
            prop_instantiate_rev;
          ] );
    ]
