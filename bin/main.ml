let usage () =
  prerr_endline
    "usage: warrant [FILE]   (reads a lean4export NDJSON file; standard input when no FILE)";
  exit 64

let () =
  Gc.set { (Gc.get ()) with Gc.space_overhead = 400; minor_heap_size = 8_388_608 };
  let ic =
    match Array.to_list Sys.argv with
    | [ _ ] -> stdin
    | [ _; "-" ] -> stdin
    | [ _; f ] -> (
        try open_in_bin f
        with Sys_error m ->
          prerr_endline m;
          exit 64)
    | _ -> usage ()
  in
  match Warrant.Check.run ic with
  | Warrant.Check.Accept ->
      print_endline "accepted";
      exit 0
  | Warrant.Check.Rejected m ->
      prerr_endline ("rejected: " ^ m);
      exit 1
  | Warrant.Check.Declined m ->
      prerr_endline ("declined: " ^ m);
      exit 2
