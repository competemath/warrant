(** The primitives the kernel accelerates by name: natural-number literals and their arithmetic.

    A name is a claim, not a fact: a file may declare its own [Nat] or [Nat.add]. A primitive is
    therefore enabled only in an environment whose constant of that name has a fingerprint
    ({!Fingerprint}) listed in {!Prim_digests}, i.e. is the genuine definition together with
    everything it depends on. Anywhere else the kernel reduces by unfolding the definitions (slowly,
    and with a work budget that ends in a decline), never by the shortcut. *)

(** Only the table generator sets this. It makes every primitive count as genuine. *)
let trust_all = ref false

let memo : (int * string, bool) Hashtbl.t = Hashtbl.create 64

let genuine env (name : string) =
  if !trust_all then Env.mem env (Name.of_dotted name)
  else
    let key = (Env.id env, name) in
    match Hashtbl.find_opt memo key with
    | Some b -> b
    | None -> (
        match List.assoc_opt name Prim_digests.table with
        | None -> false
        | Some digests -> (
            match Fingerprint.of_const env (Name.of_dotted name) with
            | Some f ->
                let ok = List.mem f digests in
                if ok then Hashtbl.replace memo key true;
                ok
            | None -> false))
