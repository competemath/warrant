open Verdict

type t = { id : int; tbl : Decl.t Name.Tbl.t; parent : t option; is_overlay : bool }

let next_id = ref 0

let fresh_id () =
  incr next_id;
  !next_id

let create () = { id = fresh_id (); tbl = Name.Tbl.create 65536; parent = None; is_overlay = false }
let id e = e.id

let rec find e n =
  match Name.Tbl.find_opt e.tbl n with
  | Some d -> Some d
  | None -> ( match e.parent with Some p -> find p n | None -> None)

let mem e n = find e n <> None
let size e = Name.Tbl.length e.tbl
let overlay e = { id = fresh_id (); tbl = Name.Tbl.create 16; parent = Some e; is_overlay = true }

let insert e (d : Decl.t) =
  if mem e d.name then reject "already declared: %s" (Name.to_string d.name);
  let rec dup = function [] -> false | p :: ps -> List.memq p ps || dup ps in
  if dup d.lparams then reject "duplicate universe parameter in %s" (Name.to_string d.name);
  Name.Tbl.replace e.tbl d.name d

let assume e d =
  if not e.is_overlay then invalid_arg "Env.assume: not an overlay";
  insert e d

let guard e what =
  if e.is_overlay then invalid_arg ("Env." ^ what ^ ": overlay environments are never committed")

let stamp e what env =
  if env <> e.id then reject "%s: evidence was derived in another environment" what

let same_lparams what a b =
  if a <> b then reject "%s: evidence holds under other universe parameters" what

let add_axiom e name lparams (ty : Evidence.Is_type.t) =
  guard e "add_axiom";
  stamp e "axiom" ty.env;
  if not ty.safe then reject "axiom: its type was checked as an unsafe declaration's";
  same_lparams "axiom" ty.lparams lparams;
  insert e { name; lparams; ty = ty.e; kind = Axiom }

let add_unsafe e name lparams (ty : Evidence.Is_type.t) =
  guard e "add_unsafe";
  stamp e "unsafe declaration" ty.env;
  same_lparams "unsafe declaration" ty.lparams lparams;
  insert e { name; lparams; ty = ty.e; kind = Unsafe_const }

(* the type, the value and the conversion of the value's type to the declared type, all about the same terms *)
let check_value what e lparams (ty : Evidence.Is_type.t) (value : Evidence.Typing.t)
    (conv : Evidence.Conv.t) =
  stamp e what ty.env;
  if not ty.safe then reject "%s: its type was checked as an unsafe declaration's" what;
  stamp e what value.env;
  stamp e what conv.env;
  same_lparams what ty.lparams lparams;
  same_lparams what value.lparams lparams;
  same_lparams what conv.lparams lparams;
  if conv.a != value.ty || conv.b != ty.e then
    reject "%s: the conversion is not between the value's type and the declared type" what

let add_def e name lparams ~hints ~(ty : Evidence.Is_type.t) ~(value : Evidence.Typing.t)
    ~(conv : Evidence.Conv.t) =
  guard e "add_def";
  check_value "definition" e lparams ty value conv;
  insert e { name; lparams; ty = ty.e; kind = Def { value = value.e; hints } }

let add_opaque e name lparams ~(ty : Evidence.Is_type.t) ~(value : Evidence.Typing.t)
    ~(conv : Evidence.Conv.t) =
  guard e "add_opaque";
  check_value "opaque" e lparams ty value conv;
  insert e { name; lparams; ty = ty.e; kind = Opaque_def { value = value.e } }

let add_thm e name lparams ~(ty : Evidence.Is_type.t) ~(prop : Evidence.Is_prop.t)
    ~(value : Evidence.Typing.t) ~(conv : Evidence.Conv.t) =
  guard e "add_thm";
  check_value "theorem" e lparams ty value conv;
  stamp e "theorem" prop.env;
  same_lparams "theorem" prop.lparams lparams;
  if prop.e != ty.e then reject "theorem: the proposition evidence is not about the declared type";
  insert e { name; lparams; ty = ty.e; kind = Thm { value = value.e } }

let add_inductive e (ev : Evidence.Ind_ok.t) =
  guard e "add_inductive";
  stamp e "inductive" ev.env;
  List.iter (insert e) ev.decls

let add_quot e (ev : Evidence.Quot_ok.t) =
  guard e "add_quot";
  stamp e "quot" ev.env;
  List.iter (insert e) ev.decls
