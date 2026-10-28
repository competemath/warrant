(** The three outcomes of a check. [Reject]: the file is not a valid environment. [Decline]: the
    checker does not cover the input (a fragment it has not implemented, a resource limit); it
    neither accepts nor claims invalidity. *)

exception Reject of string
exception Decline of string

let reject fmt = Printf.ksprintf (fun s -> raise (Reject s)) fmt
let decline fmt = Printf.ksprintf (fun s -> raise (Decline s)) fmt
