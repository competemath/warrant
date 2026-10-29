(* A coverage-guided fuzzer for the checker, in one process.

   usage (see tools/fuzz/README.md):
     dune build --profile fuzz --instrument-with bisect_ppx ./tools/fuzz/fuzz.exe
     WARRANT_FUEL=3000000 WARRANT_MAX_BITS=4194304 fuzz.exe --out DIR --seed N --seconds S SEED_FILE...

   Each round takes a file of the corpus, changes it a little (a number, a string, a key, a list, a whole line, a character), and
   runs the checker on it. The checker's own code is instrumented: a changed file that makes the checker run a line it had not
   run before joins the corpus, so the search is steered towards the parts of the checker that nothing has reached.

   What is kept (under DIR):
     corpus/       the files that reached new code
     internal/     files for which the checker said "declined: internal error" (an exception it did not plan for)
     crash/        files that made the checker raise something that escapes it
     slow/         files that took more than 5 seconds
     accepted/     files the checker accepted although the file they came from was refused (a mutation made a refused file valid,
                   which is what a soundness bug looks like); tools/fuzz_judge.py asks a second checker about each

   The checker's tables are global and grow with every run, so a long search is made of several processes of a few
   thousand runs each (tools/fuzz_run.sh). *)

open Warrant
module J = Yojson.Safe

let seed = ref 1
let seconds = ref 60.
let out_dir = ref "fuzz-out"
let share_dir = ref ""
let max_runs = ref max_int
let seeds : string list ref = ref []

let () =
  Arg.parse
    [
      ("--seed", Arg.Set_int seed, "random seed");
      ("--seconds", Arg.Set_float seconds, "wall-clock budget");
      ("--runs", Arg.Set_int max_runs, "stop after this many runs");
      ("--out", Arg.Set_string out_dir, "output directory");
      ("--share", Arg.Set_string share_dir, "directory of corpus files shared between processes");
    ]
    (fun f -> seeds := f :: !seeds)
    "fuzz.exe [options] SEED_FILE..."

let rng = Random.State.make [| !seed |]
let rint n = if n <= 0 then 0 else Random.State.int rng n
let pick a = a.(rint (Array.length a))
let coin p = Random.State.float rng 1.0 < p

let mkdir_p d =
  let rec go d =
    if d <> "" && d <> "." && d <> "/" && not (Sys.file_exists d) then (
      go (Filename.dirname d);
      try Sys.mkdir d 0o755 with Sys_error _ -> ())
  in
  go d

let read_file f =
  let ic = open_in_bin f in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  s

let write_file f s =
  let oc = open_out_bin f in
  output_string oc s;
  close_out oc

(* ---- the corpus ---- *)

type entry = { lines : J.t array; verdict : string }

let corpus : entry array ref = ref [||]
let known : (string, unit) Hashtbl.t = Hashtbl.create 4096

let parse_lines text =
  try
    Some
      (Array.of_list
         (List.filter_map
            (fun l -> if String.trim l = "" then None else Some (J.from_string l))
            (String.split_on_char '\n' text)))
  with _ -> None

let to_text lines = String.concat "\n" (Array.to_list (Array.map J.to_string lines)) ^ "\n"

(* pools of values seen in the corpus, to put them where they do not belong *)
let ints : int list ref = ref [ 0; 1; 2; 3 ]
let strings : string list ref = ref [ "" ]
let keys : string list ref = ref []
let subtrees : J.t list ref = ref []

(* the numbers seen under each key: a reference is mostly replaced by another value of the same kind of reference *)
let key_ints : (string, int list) Hashtbl.t = Hashtbl.create 64

let note_key k v =
  let l = try Hashtbl.find key_ints k with Not_found -> [] in
  if List.length l < 300 then Hashtbl.replace key_ints k (v :: l)

let rec harvest j =
  match j with
  | `Int n -> if List.length !ints < 4000 then ints := n :: !ints
  | `String s -> if List.length !strings < 2000 then strings := s :: !strings
  | `Assoc kvs ->
      if List.length !subtrees < 4000 then subtrees := j :: !subtrees;
      List.iter
        (fun (k, v) ->
          if List.length !keys < 2000 then keys := k :: !keys;
          (match v with
          | `Int n -> note_key k n
          | `List l -> List.iter (function `Int n -> note_key k n | _ -> ()) l
          | _ -> ());
          harvest v)
        kvs
  | `List l -> List.iter harvest l
  | _ -> ()

let to_array l = Array.of_list l

(* ---- the checker, run on a string ---- *)

let tmp = Filename.temp_file "fuzz" ".ndjson"

exception Timeout

let run_checker text : string * string =
  write_file tmp text;
  let ic = open_in_bin tmp in
  Sys.set_signal Sys.sigalrm (Sys.Signal_handle (fun _ -> raise Timeout));
  ignore (Unix.setitimer Unix.ITIMER_REAL { Unix.it_interval = 0.; it_value = 20. });
  let r =
    try
      match Check.run ic with
      | Check.Accept -> ("accept", "")
      | Check.Rejected m -> ("reject", m)
      | Check.Declined m -> ("decline", m)
    with
    | Timeout -> ("timeout", "")
    | e -> ("crash", Printexc.to_string e)
  in
  ignore (Unix.setitimer Unix.ITIMER_REAL { Unix.it_interval = 0.; it_value = 0. });
  close_in ic;
  r

(* ---- coverage: which points of the checker have ever been visited ---- *)

let cov = Bisect_common.coverage
let seen : (string, bool array) Hashtbl.t = Hashtbl.create 16
let total_seen = ref 0

(* the number of points visited by the run that have not been visited by any run before *)
let new_points () =
  let n = ref 0 in
  Hashtbl.iter
    (fun file (f : Bisect_common.instrumented_file) ->
      let s =
        match Hashtbl.find_opt seen file with
        | Some s -> s
        | None ->
            let s = Array.make (Array.length f.counts) false in
            Hashtbl.add seen file s;
            s
      in
      Array.iteri
        (fun i c ->
          if c > 0 && not s.(i) then (
            s.(i) <- true;
            incr n))
        f.counts)
    (Lazy.force cov);
  total_seen := !total_seen + !n;
  !n

(* ---- mutations ---- *)

let rec mutate_json j =
  match j with
  | `Int n -> (
      match rint 9 with
      | 0 -> `Int (n + 1)
      | 1 -> `Int (n - 1)
      | 2 -> `Int 0
      | 3 -> `Int 1
      | 4 -> `Int (n * 2)
      | 5 -> `Int (pick (to_array !ints))
      | 6 -> `Int (pick (to_array !ints))
      | 7 -> `Int (-1)
      | _ -> `Int (1 lsl rint 40))
  | `String s -> (
      match rint 5 with
      | 0 -> `String (pick (to_array !strings))
      | 1 -> `String ""
      | 2 -> `String (s ^ "x")
      | 3 -> `String (pick (to_array !strings))
      | _ -> `String (String.make 1 (Char.chr (rint 256))))
  | `Bool b -> `Bool (not b)
  | `Null -> `Int 0
  | `Assoc [] -> if coin 0.5 then `List [] else `Int 0
  | `Assoc kvs -> (
      let a = to_array kvs in
      let i = rint (Array.length a) in
      match rint 8 with
      | 0 ->
          `Assoc
            (List.mapi
               (fun k (key, v) -> if k = i then (pick (to_array !keys), v) else (key, v))
               kvs)
      | 1 -> `Assoc (List.filteri (fun k _ -> k <> i) kvs)
      | 2 -> `Assoc (kvs @ [ a.(i) ])
      | 3 -> `Assoc (List.rev kvs)
      | 4 when !subtrees <> [] ->
          `Assoc
            (List.mapi
               (fun k (key, v) -> if k = i then (key, pick (to_array !subtrees)) else (key, v))
               kvs)
      | _ ->
          `Assoc
            (List.mapi (fun k (key, v) -> if k = i then (key, mutate_json v) else (key, v)) kvs))
  | `List [] -> `List [ `Int (pick (to_array !ints)) ]
  | `List l -> (
      let a = to_array l in
      let i = rint (Array.length a) in
      match rint 5 with
      | 0 -> `List (List.filteri (fun k _ -> k <> i) l)
      | 1 -> `List (l @ [ a.(i) ])
      | 2 -> `List (List.rev l)
      | 3 -> `List (a.(i) :: l)
      | _ -> `List (List.mapi (fun k v -> if k = i then mutate_json v else v) l))
  | j -> j

let mutate_line_set (lines : J.t array) =
  let n = Array.length lines in
  if n = 0 then lines
  else
    match rint 10 with
    | 0 ->
        let i = rint n in
        Array.of_list (List.filteri (fun k _ -> k <> i) (Array.to_list lines))
    | 1 ->
        let i = rint n in
        Array.concat [ Array.sub lines 0 (i + 1); Array.sub lines i (n - i) ]
    | 2 when n > 1 ->
        let i = rint (n - 1) in
        let c = Array.copy lines in
        let t = c.(i) in
        c.(i) <- c.(i + 1);
        c.(i + 1) <- t;
        c
    | 3 when Array.length !corpus > 0 ->
        let other = (pick !corpus).lines in
        if Array.length other = 0 then lines
        else
          let i = rint n in
          Array.concat [ Array.sub lines 0 i; [| pick other |]; Array.sub lines i (n - i) ]
    | _ ->
        let c = Array.copy lines in
        let i = rint n in
        c.(i) <- mutate_json c.(i);
        c

let mutate_text s =
  if s = "" then s
  else
    let b = Bytes.of_string s in
    match rint 3 with
    | 0 ->
        Bytes.set b (rint (Bytes.length b)) (Char.chr (rint 256));
        Bytes.to_string b
    | 1 ->
        let i = rint (String.length s) in
        String.sub s 0 i ^ String.sub s (i + 1) (String.length s - i - 1)
    | _ ->
        let i = rint (String.length s) in
        String.sub s 0 i ^ String.make 1 (Char.chr (rint 256)) ^ String.sub s i (String.length s - i)

let child () =
  let parent = pick !corpus in
  let lines = ref parent.lines in
  for _ = 0 to rint 3 do
    lines := mutate_line_set !lines
  done;
  let text = to_text !lines in
  let text = if coin 0.05 then mutate_text text else text in
  (parent, text)

(* ---- the loop ---- *)

let counter = ref 0

let save dir name text =
  let d = Filename.concat !out_dir dir in
  mkdir_p d;
  write_file (Filename.concat d (Printf.sprintf "%d-%d-%s.ndjson" !seed !counter name)) text

let add_to_corpus text verdict =
  match parse_lines text with
  | Some lines when Array.length lines > 0 ->
      Array.iter harvest lines;
      corpus := Array.append !corpus [| { lines; verdict } |];
      true
  | _ -> false

let load_seed f =
  let text = read_file f in
  if String.length text <= 150_000 then begin
    let d = Digest.string text in
    if not (Hashtbl.mem known d) then begin
      Hashtbl.add known d ();
      let v, _ = run_checker text in
      ignore (new_points ());
      Bisect.Runtime.reset_counters ();
      ignore (add_to_corpus text v)
    end
  end

let sync_shared () =
  if !share_dir <> "" && Sys.file_exists !share_dir then
    Array.iter
      (fun f ->
        if Filename.check_suffix f ".ndjson" then
          try load_seed (Filename.concat !share_dir f) with _ -> ())
      (Sys.readdir !share_dir)

let () =
  mkdir_p !out_dir;
  if !share_dir <> "" then mkdir_p !share_dir;
  List.iter (fun f -> try load_seed f with _ -> ()) (List.rev !seeds);
  if Array.length !corpus = 0 then (
    prerr_endline "no usable seed file";
    exit 2);
  Printf.printf "seed corpus: %d files, %d points reached\n%!" (Array.length !corpus) !total_seen;
  let t0 = Unix.gettimeofday () in
  let runs = ref 0 and kept = ref 0 and internal = ref 0 and crashes = ref 0 and flipped = ref 0 in
  while Unix.gettimeofday () -. t0 < !seconds && !runs < !max_runs do
    incr runs;
    incr counter;
    let parent, text = child () in
    let d = Digest.string text in
    if not (Hashtbl.mem known d) then begin
      Hashtbl.add known d ();
      Bisect.Runtime.reset_counters ();
      let t1 = Unix.gettimeofday () in
      let v, msg = run_checker text in
      let dt = Unix.gettimeofday () -. t1 in
      let fresh = new_points () in
      if dt > 5. then save "slow" "slow" text;
      if v = "crash" || v = "timeout" then (
        incr crashes;
        save "crash" v text)
      else if v = "decline" && String.length msg >= 14 && String.sub msg 0 14 = "internal error"
      then (
        incr internal;
        save "internal" "internal" text)
      else if v = "accept" && parent.verdict <> "accept" then (
        incr flipped;
        save "accepted" "accepted" text);
      if fresh > 0 && add_to_corpus text v then (
        incr kept;
        if !share_dir <> "" then
          write_file
            (Filename.concat !share_dir (Printf.sprintf "%d-%d.ndjson" !seed !counter))
            text)
    end;
    if !runs mod 500 = 0 then begin
      Printf.printf
        "%d runs, %.0f/s, corpus %d (+%d), points %d, internal %d, crash %d, flipped-to-accept %d\n\
         %!"
        !runs
        (float !runs /. (Unix.gettimeofday () -. t0))
        (Array.length !corpus) !kept !total_seen !internal !crashes !flipped;
      if !runs mod 2000 = 0 then sync_shared ()
    end
  done;
  Printf.printf
    "done: %d runs, corpus %d, points %d, internal %d, crash %d, flipped-to-accept %d\n%!" !runs
    (Array.length !corpus) !total_seen !internal !crashes !flipped
