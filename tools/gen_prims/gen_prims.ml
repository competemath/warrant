(* Generates the fingerprints of the kernel's primitives from official lean4export files.

   usage: gen_prims FILE...   prints "name digest" lines for every primitive the file defines.

   The files are checked with every primitive trusted (the only place that switch is ever set); the digests then
   describe what the official toolchain defines. They are merged into src/prim_digests.ml by tools/gen_prims.py, and
   test/prim_test.ml checks the table against the corpora in the repository. *)

let prims =
  [
    "Nat";
    "Bool";
    "Nat.add";
    "Nat.sub";
    "Nat.mul";
    "Nat.div";
    "Nat.mod";
    "Nat.gcd";
    "Nat.beq";
    "Nat.ble";
    "Nat.land";
    "Nat.lor";
    "Nat.xor";
    "Nat.shiftLeft";
    "Nat.shiftRight";
    "Nat.pow";
    "Nat.log2";
  ]

let () =
  Warrant.Prim.trust_all := true;
  for i = 1 to Array.length Sys.argv - 1 do
    let ic = open_in_bin Sys.argv.(i) in
    let on_env env =
      List.iter
        (fun p ->
          match Warrant.Fingerprint.of_const env (Warrant.Name.of_dotted p) with
          | Some d -> Printf.printf "%s %s\n" p d
          | None -> ())
        prims
    in
    (match Warrant.Check.run ~on_env ic with
    | Warrant.Check.Accept -> ()
    | Warrant.Check.Rejected m -> Printf.eprintf "%s: rejected: %s\n" Sys.argv.(i) m
    | Warrant.Check.Declined m -> Printf.eprintf "%s: declined: %s\n" Sys.argv.(i) m);
    close_in ic
  done
