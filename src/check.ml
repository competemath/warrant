(** The driver: reads declarations in order and admits each into the environment through its
    evidence. *)

open Verdict

let trunc s = if String.length s > 700 then String.sub s 0 700 ^ "..." else s

type outcome = Accept | Rejected of string | Declined of string

let progress = Sys.getenv_opt "WARRANT_PROGRESS" <> None
let announce what name = if progress then Printf.eprintf "%s %s\n%!" what (Name.to_string name)

let admit_item env (item : Parser.item) =
  match item with
  | Parser.Meta | Parser.Table_entry -> ()
  | Parser.Axiom { name; lparams; ty; unsafe } ->
      let st = Tc.make ~allow_unsafe:unsafe env lparams in
      let ev = Tc.check_type st ty in
      if unsafe then Env.add_unsafe env name lparams ev else Env.add_axiom env name lparams ev
  | Parser.Def { name; lparams; ty; value; hints; safe } ->
      announce "def" name;
      if not safe then
        Env.add_unsafe env name lparams (Tc.check_type (Tc.make ~allow_unsafe:true env lparams) ty)
      else
        let st = Tc.make env lparams in
        let ty_ev = Tc.check_type st ty in
        let val_ev = Tc.check_typing st value in
        let conv =
          match Tc.check_conv st val_ev ty with
          | Some c -> c
          | None ->
              reject
                "definition %s: the value does not have the declared type\n\
                \ value has: %s\n\
                \ declared:  %s"
                (Name.to_string name)
                (trunc (Expr.to_string val_ev.ty))
                (trunc (Expr.to_string ty))
        in
        Env.add_def env name lparams ~hints ~ty:ty_ev ~value:val_ev ~conv
  | Parser.Opaque { name; lparams; ty; value; unsafe } ->
      if unsafe then
        Env.add_unsafe env name lparams (Tc.check_type (Tc.make ~allow_unsafe:true env lparams) ty)
      else
        let st = Tc.make env lparams in
        let ty_ev = Tc.check_type st ty in
        let val_ev = Tc.check_typing st value in
        let conv =
          match Tc.check_conv st val_ev ty with
          | Some c -> c
          | None ->
              reject
                "opaque %s: the value does not have the declared type\n\
                \ value has: %s\n\
                \ declared:  %s"
                (Name.to_string name)
                (trunc (Expr.to_string val_ev.ty))
                (trunc (Expr.to_string ty))
        in
        Env.add_opaque env name lparams ~ty:ty_ev ~value:val_ev ~conv
  | Parser.Thm { name; lparams; ty; value } ->
      announce "thm" name;
      let st = Tc.make env lparams in
      let ty_ev = Tc.check_type st ty in
      let prop =
        match Tc.check_prop st ty_ev with
        | Some p -> p
        | None -> reject "theorem %s: its type is not a proposition" (Name.to_string name)
      in
      let val_ev = Tc.check_typing st value in
      let conv =
        match Tc.check_conv st val_ev ty with
        | Some c -> c
        | None ->
            reject
              "theorem %s: the value does not have the declared type\n\
              \ value has: %s\n\
              \ declared:  %s"
              (Name.to_string name)
              (trunc (Expr.to_string val_ev.ty))
              (trunc (Expr.to_string ty))
      in
      Env.add_thm env name lparams ~ty:ty_ev ~prop ~value:val_ev ~conv
  | Parser.Quot { name; lparams; ty; kind } ->
      Env.add_quot env (Quot.admit env kind name lparams ty)
  | Parser.Inductive blk -> Env.add_inductive env (Ind.admit env blk)

let run ?(on_decl = fun (_ : int) -> ()) ?(on_env = fun (_ : Env.t) -> ()) (ic : in_channel) :
    outcome =
  let p = Parser.create () in
  let env = Env.create () in
  let count = ref 0 in
  try
    (try
       while true do
         let l = input_line ic in
         if String.length l > 0 then begin
           Tc.fuel := Tc.default_fuel;
           let item = Parser.line p l in
           (match item with
           | Parser.Meta | Parser.Table_entry -> ()
           | _ ->
               incr count;
               on_decl !count);
           admit_item env item;
           Tc.end_decl ()
         end
       done
     with End_of_file -> ());
    on_env env;
    Accept
  with
  | Reject m -> Rejected m
  | Decline m -> Declined m
  | Level.Too_complex -> Declined "universe constraint too complex to decide"
  | Stack_overflow -> Declined "stack overflow"
  | Out_of_memory -> Declined "out of memory"
  | ( Not_found | Invalid_argument _ | Failure _ | Assert_failure _ | Match_failure _
    | Division_by_zero ) as e ->
      (* an internal fault is a decline, written out, never an accepted file and never the runtime's own exit code *)
      Declined ("internal error: " ^ Printexc.to_string e)
