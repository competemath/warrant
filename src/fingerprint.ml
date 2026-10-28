(** Content fingerprints of declarations.

    The fingerprint of a constant is a BLAKE2b-256 digest of its kind, universe parameters, type and
    (for definitions, theorems and opaque constants) value, together with the fingerprints of every
    constant those mention. Two environments whose constants have equal fingerprints have the same
    constant, all the way down: a file cannot redefine a helper under a genuine name and keep the
    genuine fingerprint. Reducibility hints are left out (they steer the order of unfolding, never
    the meaning).

    The kernel's arithmetic shortcuts are enabled only for constants whose fingerprint appears in
    {!Prim_digests}. *)

let memo : (int * int, string) Hashtbl.t = Hashtbl.create 64

let rec of_const_aux env in_progress (n : Name.t) : string option =
  match Env.find env n with
  | None -> None
  | Some d -> (
      let key = (Env.id env, n.id) in
      match Hashtbl.find_opt memo key with
      | Some f -> Some f
      | None ->
          let b = Buffer.create 256 in
          let add s =
            Buffer.add_string b s;
            Buffer.add_char b '\n'
          in
          let term e = add (Expr.to_string e) in
          let deps_of es =
            List.iter
              (fun e ->
                List.iter
                  (fun c ->
                    if c != n then
                      if List.memq c !in_progress then add ("dep " ^ Name.to_string c ^ " (cyclic)")
                      else
                        match of_const_aux env in_progress c with
                        | Some f -> add ("dep " ^ Name.to_string c ^ " " ^ f)
                        | None -> add ("dep " ^ Name.to_string c ^ " (absent)"))
                  (Expr.consts e))
              es
          in
          in_progress := n :: !in_progress;
          add (Name.to_string n);
          add (String.concat "," (List.map Name.to_string d.lparams));
          term d.ty;
          let terms =
            match d.kind with
            | Decl.Axiom ->
                add "axiom";
                [ d.ty ]
            | Decl.Unsafe_const ->
                add "unsafe";
                [ d.ty ]
            | Decl.Def { value; _ } ->
                add "def";
                term value;
                [ d.ty; value ]
            | Decl.Thm { value } ->
                add "thm";
                term value;
                [ d.ty; value ]
            | Decl.Opaque_def { value } ->
                add "opaque";
                term value;
                [ d.ty; value ]
            | Decl.Quot _ ->
                add "quot";
                [ d.ty ]
            | Decl.Induct i ->
                add (Printf.sprintf "induct %d %d" i.nparams i.nindices);
                List.iter
                  (fun c ->
                    add ("ctor " ^ Name.to_string c);
                    match of_const_aux env in_progress c with
                    | Some f -> add f
                    | None -> add "(absent)")
                  i.ctors;
                [ d.ty ]
            | Decl.Ctor c ->
                add
                  (Printf.sprintf "ctor %s %d %d %d" (Name.to_string c.induct) c.cidx c.cparams
                     c.nfields);
                [ d.ty ]
            | Decl.Rec r ->
                add
                  (Printf.sprintf "rec %d %d %d %d %b" r.rparams r.rindices r.nmotives r.nminors r.k);
                List.iter
                  (fun (ru : Decl.rule) ->
                    add (Name.to_string ru.ctor);
                    term ru.rhs)
                  r.rules;
                d.ty :: List.map (fun (ru : Decl.rule) -> ru.rhs) r.rules
          in
          deps_of terms;
          in_progress := List.filter (fun m -> m != n) !in_progress;
          let f = Digest.BLAKE256.to_hex (Digest.BLAKE256.string (Buffer.contents b)) in
          Hashtbl.replace memo key f;
          Some f)

let of_const env n = of_const_aux env (ref []) n
