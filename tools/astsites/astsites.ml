(* Lists the places of an OCaml source file where tools/mutate.py --ast may plant a mutation, as a JSON array of
   {start, end, repl, kind, line}: replace the bytes [start, end) with [repl]. The syntax tree is only used to find the
   places and their extent; the replacement is built from slices of the original text, so layout and comments stay.

   usage: astsites FILE [INFO_FILE...]
   INFO_FILEs (the project's other sources) tell which constructors and record fields may stand for each other. *)

open Parsetree

let read path =
  let ic = open_in_bin path in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  s

let parse path src =
  let lb = Lexing.from_string src in
  Location.init lb path;
  Parse.implementation lb

(* constructors: name -> (type, arity); a name declared twice in the project is ambiguous and left out *)
let ctors : (string, string * int) Hashtbl.t = Hashtbl.create 64
let ambiguous : (string, unit) Hashtbl.t = Hashtbl.create 8

(* record fields: name -> (type, printed field type) *)
let fields : (string, string * string) Hashtbl.t = Hashtbl.create 64

let collect_types str =
  let it =
    {
      Ast_iterator.default_iterator with
      type_declaration =
        (fun self td ->
          let tname = td.ptype_name.txt in
          (match td.ptype_kind with
          | Ptype_variant cds ->
              List.iter
                (fun cd ->
                  let arity =
                    match cd.pcd_args with Pcstr_tuple l -> List.length l | Pcstr_record _ -> -1
                  in
                  let n = cd.pcd_name.txt in
                  if Hashtbl.mem ctors n then Hashtbl.replace ambiguous n ()
                  else Hashtbl.replace ctors n (tname, arity))
                cds
          | Ptype_record lds ->
              List.iter
                (fun ld ->
                  let n = ld.pld_name.txt in
                  let ty = Format.asprintf "%a" Pprintast.core_type ld.pld_type in
                  if Hashtbl.mem fields n then Hashtbl.replace ambiguous ("." ^ n) ()
                  else Hashtbl.replace fields n (tname, ty))
                lds
          | _ -> ());
          Ast_iterator.default_iterator.type_declaration self td);
    }
  in
  it.structure it str

let sibling_ctors n =
  match Hashtbl.find_opt ctors n with
  | Some (t, a) when a >= 0 && not (Hashtbl.mem ambiguous n) ->
      Hashtbl.fold
        (fun m (t', a') acc ->
          if m <> n && t' = t && a' = a && not (Hashtbl.mem ambiguous m) then m :: acc else acc)
        ctors []
  | _ -> []

let sibling_fields n =
  match Hashtbl.find_opt fields n with
  | Some (t, ty) when not (Hashtbl.mem ambiguous ("." ^ n)) ->
      Hashtbl.fold
        (fun m (t', ty') acc ->
          if m <> n && t' = t && ty' = ty && not (Hashtbl.mem ambiguous ("." ^ m)) then m :: acc
          else acc)
        fields []
  | _ -> []

let ops_cmp = [ "="; "<>"; "=="; "!="; "<"; "<="; ">"; ">=" ]

let () =
  let file = Sys.argv.(1) in
  let src = read file in
  for i = 2 to Array.length Sys.argv - 1 do
    try collect_types (parse Sys.argv.(i) (read Sys.argv.(i))) with _ -> ()
  done;
  let str = parse file src in
  collect_types str;
  let out = ref [] in
  let strs = ref [] in
  let sl (l : Location.t) =
    String.sub src l.loc_start.pos_cnum (l.loc_end.pos_cnum - l.loc_start.pos_cnum)
  in
  let add kind (l : Location.t) repl =
    if not l.loc_ghost then
      out :=
        `Assoc
          [
            ("start", `Int l.loc_start.pos_cnum);
            ("end", `Int l.loc_end.pos_cnum);
            ("repl", `String repl);
            ("kind", `String kind);
            ("line", `Int l.loc_start.pos_lnum);
          ]
        :: !out
  in
  let paren s = "(" ^ s ^ ")" in
  (* strings that are messages or formats are left alone: the tests pin the message of every refusal separately *)
  let skip_strings : (int, unit) Hashtbl.t = Hashtbl.create 64 in
  let message_fns =
    [
      "reject";
      "decline";
      "malformed";
      "failwith";
      "invalid_arg";
      "sprintf";
      "eprintf";
      "printf";
      "ksprintf";
      "prerr_endline";
      "print_endline";
      "announce";
    ]
  in
  let bool_name n =
    let starts p = String.length n >= String.length p && String.sub n 0 (String.length p) = p in
    List.exists starts
      [ "is_"; "has_"; "can_"; "nat_ok"; "same_"; "closed"; "valid"; "mem"; "equal" ]
  in
  let is_op (e : expression) names =
    match e.pexp_desc with
    | Pexp_ident { txt = Longident.Lident n; _ } -> List.mem n names
    | _ -> false
  in
  let positional args = List.for_all (fun (l, _) -> l = Asttypes.Nolabel) args in
  let cond_mutants kind (c : expression) =
    add (kind ^ "-true") c.pexp_loc "true";
    add (kind ^ "-false") c.pexp_loc "false";
    add (kind ^ "-not") c.pexp_loc ("not " ^ paren (sl c.pexp_loc))
  in
  let case_mutants (cases : case list) =
    List.iter
      (fun (c : case) ->
        match c.pc_guard with
        | Some g ->
            add "guard-true" g.pexp_loc "true";
            add "guard-false" g.pexp_loc "false"
        | None -> ())
      cases;
    (* the right-hand side of a case replaced by that of its neighbour *)
    let arr = Array.of_list cases in
    for i = 0 to Array.length arr - 2 do
      let a = arr.(i).pc_rhs and b = arr.(i + 1).pc_rhs in
      let ta = sl a.pexp_loc and tb = sl b.pexp_loc in
      if ta <> tb && String.length ta < 120 && String.length tb < 120 then (
        add "arm-next" a.pexp_loc (paren tb);
        add "arm-prev" b.pexp_loc (paren ta))
    done
  in
  let expr self (e : expression) =
    (match e.pexp_desc with
    | Pexp_ifthenelse (c, a, eo) -> (
        cond_mutants "if" c;
        match eo with
        | Some b ->
            add "branch-swap" e.pexp_loc
              (paren
                 ("if " ^ sl c.pexp_loc ^ " then "
                 ^ paren (sl b.pexp_loc)
                 ^ " else "
                 ^ paren (sl a.pexp_loc)));
            add "take-then" e.pexp_loc (paren (sl a.pexp_loc));
            add "take-else" e.pexp_loc (paren (sl b.pexp_loc))
        | None -> ())
    | Pexp_apply (f, [ (_, l); (_, r) ]) when is_op f [ "&&"; "||" ] ->
        add "operand-left" e.pexp_loc (paren (sl l.pexp_loc));
        add "operand-right" e.pexp_loc (paren (sl r.pexp_loc));
        add "bool-true" e.pexp_loc "true";
        add "bool-false" e.pexp_loc "false"
    | Pexp_apply (f, [ _; _ ]) when is_op f ops_cmp ->
        add "cmp-true" e.pexp_loc "true";
        add "cmp-false" e.pexp_loc "false"
    | Pexp_apply (f, [ (_, x) ]) when is_op f [ "not" ] ->
        add "not-drop" e.pexp_loc (paren (sl x.pexp_loc))
    | Pexp_apply
        ({ pexp_desc = Pexp_ident { txt = Longident.Lident n | Longident.Ldot (_, n); _ }; _ }, args)
      when List.mem n message_fns ->
        List.iter
          (fun (_, (a : expression)) ->
            match a.pexp_desc with
            | Pexp_constant _ -> Hashtbl.replace skip_strings a.pexp_loc.loc_start.pos_cnum ()
            | _ -> ())
          args
    | Pexp_apply (f, args)
      when (match f.pexp_desc with Pexp_ident _ -> true | _ -> false)
           && (not
                 (is_op f
                    ([ "&&"; "||"; "not"; "@@"; "|>"; "^"; "@"; "+"; "-"; "*"; "/"; "::" ] @ ops_cmp)))
           && positional args
           && List.length args >= 2 ->
        let a = Array.of_list (List.map snd args) in
        for i = 0 to Array.length a - 2 do
          if sl a.(i).pexp_loc <> sl a.(i + 1).pexp_loc then
            let parts =
              Array.mapi
                (fun j x ->
                  let k = if j = i then i + 1 else if j = i + 1 then i else j in
                  paren (sl a.(k).pexp_loc) |> fun s ->
                  ignore x;
                  s)
                a
            in
            add "args-swap" e.pexp_loc
              (paren (sl f.pexp_loc ^ " " ^ String.concat " " (Array.to_list parts)))
        done
    | Pexp_sequence (a, _) -> (
        match a.pexp_desc with
        | Pexp_construct ({ txt = Longident.Lident "()"; _ }, None) -> ()
        | _ -> add "stmt-delete" a.pexp_loc "()")
    | Pexp_constant { pconst_desc = Pconst_integer (s, None); _ } -> (
        match int_of_string_opt s with
        | Some n ->
            add "int-succ" e.pexp_loc (string_of_int (n + 1));
            if n > 0 then add "int-pred" e.pexp_loc (string_of_int (n - 1))
        | None -> ())
    | Pexp_constant { pconst_desc = Pconst_string (str, _, None); _ }
      when (not (Hashtbl.mem skip_strings e.pexp_loc.loc_start.pos_cnum))
           && String.length str >= 1
           && String.length str <= 80
           && (not (String.contains str '%'))
           && not (String.contains str '\n') ->
        strs := (e.pexp_loc, str) :: !strs;
        add "str-change" e.pexp_loc ("\"" ^ String.escaped str ^ "~\"")
    | Pexp_construct ({ txt = Longident.Lident "Some"; _ }, Some _) ->
        add "some-none" e.pexp_loc "None"
    | Pexp_construct (lid, _) ->
        let n = Longident.last lid.txt in
        let s = sl lid.loc in
        List.iter
          (fun m ->
            if String.length s >= String.length n then
              add "ctor-swap" lid.loc (String.sub s 0 (String.length s - String.length n) ^ m))
          (sibling_ctors n)
    | Pexp_field (_, lid) -> (
        match lid.txt with
        | Longident.Lident n -> List.iter (fun m -> add "field-swap" lid.loc m) (sibling_fields n)
        | _ -> ())
    | Pexp_for (_, lo, hi, _, _) ->
        add "for-lo-succ" lo.pexp_loc (paren (sl lo.pexp_loc ^ " + 1"));
        add "for-hi-pred" hi.pexp_loc (paren (sl hi.pexp_loc ^ " - 1"));
        add "for-hi-succ" hi.pexp_loc (paren (sl hi.pexp_loc ^ " + 1"))
    | Pexp_match (_, cases) | Pexp_try (_, cases) -> case_mutants cases
    | Pexp_function (_, _, Pfunction_cases (cases, _, _)) -> case_mutants cases
    | _ -> ());
    Ast_iterator.default_iterator.expr self e
  in
  let pat self (p : pattern) =
    (match p.ppat_desc with
    | Ppat_construct (lid, _) ->
        let n = Longident.last lid.txt in
        let s = sl lid.loc in
        List.iter
          (fun m ->
            if String.length s >= String.length n then
              add "ctor-swap-pat" lid.loc (String.sub s 0 (String.length s - String.length n) ^ m))
          (sibling_ctors n)
    | _ -> ());
    Ast_iterator.default_iterator.pat self p
  in
  let structure_item self (si : structure_item) =
    (match si.pstr_desc with
    | Pstr_value (_, vbs) ->
        List.iter
          (fun (vb : value_binding) ->
            match vb.pvb_pat.ppat_desc with
            | Ppat_var { txt = n; _ } when bool_name n ->
                let body =
                  match vb.pvb_expr.pexp_desc with
                  | Pexp_function (_, _, Pfunction_body b) -> b
                  | _ -> vb.pvb_expr
                in
                add "fun-true" body.pexp_loc "true";
                add "fun-false" body.pexp_loc "false"
            | _ -> ())
          vbs
    | _ -> ());
    Ast_iterator.default_iterator.structure_item self si
  in
  let it = { Ast_iterator.default_iterator with expr; pat; structure_item } in
  it.structure it str;
  (* two string constants exchanged: kinds of declaration that share a tag, primitives that share a name *)
  let arr = Array.of_list (List.rev !strs) in
  Array.iteri
    (fun i ((l : Location.t), a) ->
      if i + 1 < Array.length arr then
        let l2, b = arr.(i + 1) in
        if a <> b then (
          add "str-swap" l ("\"" ^ String.escaped b ^ "\"");
          add "str-swap" l2 ("\"" ^ String.escaped a ^ "\"")))
    arr;
  print_string (Yojson.Safe.to_string (`List (List.rev !out)))
