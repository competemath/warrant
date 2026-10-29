(** Reads the lean4export NDJSON format (3.1.x) one line at a time. Table references ([in], [il],
    [ie]) are looked up in hash tables, so sparse and out-of-order indices are fine; a reference to
    an index that was never defined is a rejection. Metadata fields that the format carries for
    convenience are returned as claims. *)

open Verdict
module J = Yojson.Safe

type item =
  | Meta
  | Table_entry
  | Axiom of { name : Name.t; lparams : Name.t list; ty : Expr.t; unsafe : bool }
  | Def of {
      name : Name.t;
      lparams : Name.t list;
      ty : Expr.t;
      value : Expr.t;
      hints : Decl.hints;
      safe : bool;
    }
  | Thm of { name : Name.t; lparams : Name.t list; ty : Expr.t; value : Expr.t }
  | Opaque of { name : Name.t; lparams : Name.t list; ty : Expr.t; value : Expr.t; unsafe : bool }
  | Quot of { name : Name.t; lparams : Name.t list; ty : Expr.t; kind : Decl.quot_kind }
  | Inductive of Claim.block

type t = {
  names : (int, Name.t) Hashtbl.t;
  levels : (int, Level.t) Hashtbl.t;
  exprs : (int, Expr.t) Hashtbl.t;
}

let create () =
  let names = Hashtbl.create 4096 and levels = Hashtbl.create 4096 in
  Hashtbl.add names 0 Name.anon;
  Hashtbl.add levels 0 Level.zero;
  { names; levels; exprs = Hashtbl.create 65536 }

let malformed fmt = Printf.ksprintf (fun s -> decline "malformed input: %s" s) fmt
let field o k = match List.assoc_opt k o with Some v -> v | None -> malformed "missing field %s" k
let to_int = function `Int i -> i | j -> malformed "expected an integer, got %s" (J.to_string j)

(* every count, index and position in the format is a natural number *)
let to_nat = function
  | `Int i when i >= 0 -> i
  | j -> malformed "expected a natural number, got %s" (J.to_string j)

let to_bool = function `Bool b -> b | j -> malformed "expected a boolean, got %s" (J.to_string j)
let to_str = function `String s -> s | j -> malformed "expected a string, got %s" (J.to_string j)
let to_list = function `List l -> l | j -> malformed "expected a list, got %s" (J.to_string j)

(* an object with a repeated key is read differently by different tools: refuse it rather than pick one reading *)
let to_obj = function
  | `Assoc o ->
      let rec dup = function [] -> false | (k, _) :: rest -> List.mem_assoc k rest || dup rest in
      if dup o then malformed "duplicate key in an object";
      o
  | j -> malformed "expected an object, got %s" (J.to_string j)

let geti o k = to_int (field o k)
let getn o k = to_nat (field o k)

let lookup tbl what i =
  match Hashtbl.find_opt tbl i with Some v -> v | None -> reject "dangling %s reference %d" what i

let name p i = lookup p.names "name" i
let level p i = lookup p.levels "level" i
let expr p i = lookup p.exprs "expression" i

let define tbl what i v =
  if Hashtbl.mem tbl i then reject "%s index %d defined twice" what i;
  Hashtbl.add tbl i v

let names_of p j = List.map (fun x -> name p (to_int x)) (to_list j)

let hints_of = function
  | `String "opaque" -> Decl.Opaque
  | `String "abbrev" -> Decl.Abbrev
  | `Assoc [ ("regular", `Int h) ] when h >= 0 -> Decl.Regular h
  | j -> malformed "unknown reducibility hints %s" (J.to_string j)

let quot_kind_of = function
  | `String "type" -> Decl.QType
  | `String "ctor" -> Decl.QCtor
  | `String "lift" -> Decl.QLift
  | `String "ind" -> Decl.QInd
  | j -> malformed "unknown quotient kind %s" (J.to_string j)

let parse_expr p kind v =
  match kind with
  | "bvar" -> Expr.bvar (to_nat v)
  | "sort" -> Expr.sort (level p (to_int v))
  | "const" ->
      let o = to_obj v in
      Expr.const
        (name p (geti o "name"))
        (List.map (fun x -> level p (to_int x)) (to_list (field o "us")))
  | "app" ->
      let o = to_obj v in
      Expr.app (expr p (geti o "fn")) (expr p (geti o "arg"))
  | "lam" ->
      let o = to_obj v in
      Expr.lam (expr p (geti o "type")) (expr p (geti o "body"))
  | "forallE" ->
      let o = to_obj v in
      Expr.pi (expr p (geti o "type")) (expr p (geti o "body"))
  | "letE" ->
      let o = to_obj v in
      Expr.let_ (expr p (geti o "type")) (expr p (geti o "value")) (expr p (geti o "body"))
  | "proj" ->
      let o = to_obj v in
      Expr.proj (name p (geti o "typeName")) (getn o "idx") (expr p (geti o "struct"))
  | "natVal" ->
      (* digits only: Z.of_string would also take a sign and a 0x prefix *)
      let digits = to_str v in
      if digits = "" || not (String.for_all (fun c -> c >= '0' && c <= '9') digits) then
        malformed "bad natural literal";
      Expr.nat (Z.of_string digits)
  | "strVal" -> Expr.str (to_str v)
  | "mdata" -> expr p (geti (to_obj v) "expr")
  | k -> malformed "unknown expression kind %s" k

let parse_level p kind v =
  match kind with
  | "succ" -> Level.succ (level p (to_int v))
  | "max" | "imax" -> (
      match to_list v with
      | [ a; b ] ->
          let a = level p (to_int a) and b = level p (to_int b) in
          if kind = "max" then Level.max a b else Level.imax a b
      | _ -> malformed "level %s needs two operands" kind)
  | "param" -> Level.param (name p (to_int v))
  | k -> malformed "unknown level kind %s" k

let parse_ind p o =
  let types =
    List.map
      (fun j ->
        let o = to_obj j in
        {
          Claim.name = name p (geti o "name");
          lparams = names_of p (field o "levelParams");
          ty = expr p (geti o "type");
          all = names_of p (field o "all");
          ctors = names_of p (field o "ctors");
          nparams = getn o "numParams";
          nindices = getn o "numIndices";
          is_rec = to_bool (field o "isRec");
          is_reflexive = to_bool (field o "isReflexive");
          nnested = getn o "numNested";
          unsafe = to_bool (field o "isUnsafe");
        })
      (to_list (field o "types"))
  in
  let ctor_decls =
    List.map
      (fun j ->
        let o = to_obj j in
        {
          Claim.cname = name p (geti o "name");
          clparams = names_of p (field o "levelParams");
          cty = expr p (geti o "type");
          induct = name p (geti o "induct");
          cidx = getn o "cidx";
          cnparams = getn o "numParams";
          nfields = getn o "numFields";
          cunsafe = to_bool (field o "isUnsafe");
        })
      (to_list (field o "ctors"))
  in
  let recs =
    List.map
      (fun j ->
        let o = to_obj j in
        {
          Claim.rname = name p (geti o "name");
          rlparams = names_of p (field o "levelParams");
          rty = expr p (geti o "type");
          rall = names_of p (field o "all");
          rnparams = getn o "numParams";
          rnindices = getn o "numIndices";
          nmotives = getn o "numMotives";
          nminors = getn o "numMinors";
          rules =
            List.map
              (fun r ->
                let r = to_obj r in
                {
                  Claim.ctor = name p (geti r "ctor");
                  nfields = getn r "nfields";
                  rhs = expr p (geti r "rhs");
                })
              (to_list (field o "rules"));
          k = to_bool (field o "k");
          runsafe = to_bool (field o "isUnsafe");
        })
      (to_list (field o "recs"))
  in
  Inductive { Claim.types; ctor_decls; recs }

let parse_decl p kind o =
  let nm () = name p (geti o "name") and lps () = names_of p (field o "levelParams") in
  match kind with
  | "axiom" ->
      Axiom
        {
          name = nm ();
          lparams = lps ();
          ty = expr p (geti o "type");
          unsafe = to_bool (field o "isUnsafe");
        }
  | "def" ->
      Def
        {
          name = nm ();
          lparams = lps ();
          ty = expr p (geti o "type");
          value = expr p (geti o "value");
          hints = hints_of (field o "hints");
          safe = (match field o "safety" with `String "safe" -> true | _ -> false);
        }
  | "thm" ->
      Thm
        {
          name = nm ();
          lparams = lps ();
          ty = expr p (geti o "type");
          value = expr p (geti o "value");
        }
  | "opaque" ->
      Opaque
        {
          name = nm ();
          lparams = lps ();
          ty = expr p (geti o "type");
          value = expr p (geti o "value");
          unsafe = to_bool (field o "isUnsafe");
        }
  | "quot" ->
      Quot
        {
          name = nm ();
          lparams = lps ();
          ty = expr p (geti o "type");
          kind = quot_kind_of (field o "kind");
        }
  | "inductive" -> parse_ind p o
  | k -> malformed "unknown declaration kind %s" k

let check_meta o =
  let fmt = to_obj (field o "format") in
  let v = to_str (field fmt "version") in
  match String.split_on_char '.' v with
  | "3" :: "1" :: _ -> ()
  | _ -> decline "export format version %s is not supported (3.1.x is)" v

let line p (s : string) : item =
  let j = try J.from_string s with Yojson.Json_error m -> malformed "not valid JSON: %s" m in
  let o = to_obj j in
  match o with
  | [ ("meta", m) ] ->
      check_meta (to_obj m);
      Meta
  | _ -> (
      match (List.assoc_opt "in" o, List.assoc_opt "il" o, List.assoc_opt "ie" o) with
      | Some i, _, _ -> (
          let i = to_int i in
          match List.filter (fun (k, _) -> k <> "in") o with
          | [ ("str", v) ] ->
              let v = to_obj v in
              define p.names "name" i (Name.str (name p (geti v "pre")) (to_str (field v "str")));
              Table_entry
          | [ ("num", v) ] ->
              let v = to_obj v in
              define p.names "name" i (Name.num (name p (geti v "pre")) (geti v "i"));
              Table_entry
          | _ -> malformed "bad name entry")
      | _, Some i, _ -> (
          let i = to_int i in
          match List.filter (fun (k, _) -> k <> "il") o with
          | [ (kind, v) ] ->
              define p.levels "level" i (parse_level p kind v);
              Table_entry
          | _ -> malformed "bad level entry")
      | _, _, Some i -> (
          let i = to_int i in
          match List.filter (fun (k, _) -> k <> "ie") o with
          | [ (kind, v) ] ->
              define p.exprs "expression" i (Expr.permanently (fun () -> parse_expr p kind v));
              Table_entry
          | _ -> malformed "bad expression entry")
      | None, None, None -> (
          match o with [ (kind, v) ] -> parse_decl p kind (to_obj v) | _ -> malformed "bad line"))
