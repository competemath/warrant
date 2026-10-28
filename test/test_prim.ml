(* The kernel's name-keyed shortcuts are enabled only for genuine definitions. *)

open Warrant

let corpus f = Filename.concat (Filename.concat (Filename.concat "../tests" "arena") "good") f

let check_file ?(trust = false) f =
  Prim.trust_all := trust;
  let ic = open_in_bin (corpus f) in
  let r = Check.run ic in
  close_in ic;
  Prim.trust_all := false;
  r

(* the primitives of an official Init export (toolchain 4.34.0-rc2), cut with tools/slice.py: the source of every digest
   that no other corpus file defines (gcd, land, lor, xor, shifts, log2, ...) *)
let prims_file = Filename.concat (Filename.concat "../tests" "prims") "init-4.34.0-rc2.ndjson"
let accepted = function Check.Accept -> true | _ -> false

(* with the digests of the genuine definitions in the table, the official files that use literals are accepted *)
let genuine_accepted () =
  List.iter
    (fun f -> Alcotest.(check bool) f true (accepted (check_file f)))
    [
      "other/nat-lit-add.ndjson";
      "other/nat-lit-sub.ndjson";
      "other/nat-lit-ble.ndjson";
      "tutorial/102_aNatLit.ndjson";
    ];
  (* the primitives file is itself accepted without trusting any name: its definitions are the genuine ones *)
  let ic = open_in_bin prims_file in
  let r = Check.run ic in
  close_in ic;
  Alcotest.(check bool) "init primitives" true (accepted r)

(* every digest in the table is the digest of an official definition found in the corpus *)
let table_matches_corpus () =
  let found : (string, string) Hashtbl.t = Hashtbl.create 16 in
  let files =
    [
      "init-prelude.ndjson";
      "other/nat-lit-add.ndjson";
      "other/nat-lit-ble.ndjson";
      "other/nat-lit-sub.ndjson";
    ]
  in
  List.iter
    (fun path ->
      Prim.trust_all := true;
      let ic = open_in_bin path in
      ignore
        (Check.run
           ~on_env:(fun env ->
             List.iter
               (fun (name, _) ->
                 match Fingerprint.of_const env (Name.of_dotted name) with
                 | Some d -> Hashtbl.replace found (name ^ " " ^ d) name
                 | None -> ())
               Prim_digests.table)
           ic);
      close_in ic;
      Prim.trust_all := false)
    (prims_file :: List.map corpus files);
  Hashtbl.iter
    (fun key name ->
      let digest = List.nth (String.split_on_char ' ' key) 1 in
      Alcotest.(check bool)
        (name ^ " is in the table") true
        (List.mem digest (List.assoc name Prim_digests.table)))
    found;
  Alcotest.(check bool) "the corpus covers some primitives" true (Hashtbl.length found > 0);
  (* and the other way round: no digest in the table lacks an official definition behind it *)
  List.iter
    (fun (name, digests) ->
      List.iter
        (fun d ->
          Alcotest.(check bool)
            (name ^ " " ^ d ^ " has a source")
            true
            (Hashtbl.mem found (name ^ " " ^ d)))
        digests)
    Prim_digests.table

(* the negative control: the same file that is rejected with fingerprints is accepted when every name is trusted, which
   is the unsoundness the fingerprints close *)
let negative_control () =
  let path = Filename.concat (Filename.concat "../tests" "regressions") "fake-nat-add.ndjson" in
  let run trust =
    Prim.trust_all := trust;
    let ic = open_in_bin path in
    let r = Check.run ic in
    close_in ic;
    Prim.trust_all := false;
    r
  in
  Alcotest.(check bool) "rejected with fingerprints" false (accepted (run false));
  Alcotest.(check bool) "accepted when names are trusted" true (accepted (run true))

let () =
  Alcotest.run "prim"
    [
      ( "primitives",
        [
          Alcotest.test_case "genuine definitions enable literals" `Quick genuine_accepted;
          Alcotest.test_case "table entries match official exports" `Quick table_matches_corpus;
          Alcotest.test_case "negative control: trusting names is unsound" `Quick negative_control;
        ] );
    ]
