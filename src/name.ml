type t = { id : int; node : node }
and node = Anon | Str of t * string | Num of t * int

let anon = { id = 0; node = Anon }
let counter = ref 1
let str_tbl : (int * string, t) Hashtbl.t = Hashtbl.create 4096
let num_tbl : (int * int, t) Hashtbl.t = Hashtbl.create 64

let fresh node =
  let n = { id = !counter; node } in
  incr counter;
  n

let str p s =
  match Hashtbl.find_opt str_tbl (p.id, s) with
  | Some n -> n
  | None ->
      let n = fresh (Str (p, s)) in
      Hashtbl.add str_tbl (p.id, s) n;
      n

let num p i =
  match Hashtbl.find_opt num_tbl (p.id, i) with
  | Some n -> n
  | None ->
      let n = fresh (Num (p, i)) in
      Hashtbl.add num_tbl (p.id, i) n;
      n

let equal (a : t) (b : t) = a == b
let compare a b = Int.compare a.id b.id
let hash a = a.id

let rec to_string n =
  match n.node with
  | Anon -> "[anonymous]"
  | Str ({ node = Anon; _ }, s) -> s
  | Num ({ node = Anon; _ }, i) -> string_of_int i
  | Str (p, s) -> to_string p ^ "." ^ s
  | Num (p, i) -> to_string p ^ "." ^ string_of_int i

let of_dotted s = List.fold_left str anon (String.split_on_char '.' s)
let prefix n = match n.node with Anon -> anon | Str (p, _) | Num (p, _) -> p

let rec replace_prefix n old nw =
  if n == old then nw
  else
    match n.node with
    | Anon -> n
    | Str (p, s) -> str (replace_prefix p old nw) s
    | Num (p, i) -> num (replace_prefix p old nw) i

module Tbl = Hashtbl.Make (struct
  type nonrec t = t

  let equal = equal
  let hash = hash
end)
