(* Questions the type checker answers about terms that no file can pose: its answers are part of what it promises, and a mutation of
   one of them is invisible to every file (the comparison of two proofs of different propositions, which a well-typed file never
   asks, is one). The environment is built by checking a small file, then the checker is asked directly. *)

open Warrant

let file =
  String.concat "\n"
    [
      {|{"meta":{"exporter":{"name":"t","version":"0"},"format":{"version":"3.1.0"},"lean":{"githash":"0","version":"4.29.1"}}}|};
      {|{"in":1,"str":{"pre":0,"str":"P"}}|};
      {|{"in":2,"str":{"pre":0,"str":"Q"}}|};
      {|{"in":3,"str":{"pre":0,"str":"p"}}|};
      {|{"in":4,"str":{"pre":0,"str":"p2"}}|};
      {|{"in":5,"str":{"pre":0,"str":"q"}}|};
      {|{"ie":0,"sort":0}|};
      {|{"ie":1,"const":{"name":1,"us":[]}}|};
      {|{"ie":2,"const":{"name":2,"us":[]}}|};
      {|{"axiom":{"isUnsafe":false,"levelParams":[],"name":1,"type":0}}|};
      {|{"axiom":{"isUnsafe":false,"levelParams":[],"name":2,"type":0}}|};
      {|{"axiom":{"isUnsafe":false,"levelParams":[],"name":3,"type":1}}|};
      {|{"axiom":{"isUnsafe":false,"levelParams":[],"name":4,"type":1}}|};
      {|{"axiom":{"isUnsafe":false,"levelParams":[],"name":5,"type":2}}|};
    ]
  ^ "\n"

let with_env f =
  let path = Filename.temp_file "internal" ".ndjson" in
  let oc = open_out_bin path in
  output_string oc file;
  close_out oc;
  let ic = open_in_bin path in
  let ran = ref false in
  (match
     Check.run
       ~on_env:(fun env ->
         ran := true;
         f env)
       ic
   with
  | Check.Accept -> ()
  | _ -> Alcotest.fail "the small file is not accepted");
  close_in ic;
  Sys.remove path;
  Alcotest.(check bool) "the environment was handed over" true !ran

let c s = Expr.const (Name.of_dotted s) []

(* two proofs of one proposition are one; a proof of P and a proof of Q are not, whatever else is true of them *)
let proof_irrelevance () =
  with_env (fun env ->
      let st = Tc.make env [] in
      Alcotest.(check bool) "p = p2 (both proofs of P)" true (Tc.is_def_eq st (c "p") (c "p2"));
      Alcotest.(check bool) "p = q (proofs of P and of Q)" false (Tc.is_def_eq st (c "p") (c "q"));
      Alcotest.(check bool) "q = p" false (Tc.is_def_eq st (c "q") (c "p"));
      Alcotest.(check bool)
        "P = Q (the propositions themselves)" false
        (Tc.is_def_eq st (c "P") (c "Q")))

let () =
  Alcotest.run "internal"
    [
      ( "type checker",
        [ Alcotest.test_case "proof irrelevance compares the types" `Quick proof_irrelevance ] );
    ]
