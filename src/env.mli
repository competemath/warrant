(** The environment: the constants admitted so far. It can only grow, and only through the [add_*]
    functions, each of which demands the evidence for exactly what it adds and checks that the
    evidence was derived in this environment (stamps) and is about this declaration. *)

type t

val create : unit -> t
val id : t -> Evidence.env_id
val find : t -> Name.t -> Decl.t option
val mem : t -> Name.t -> bool
val size : t -> int

val overlay : t -> t
(** A scratch extension used while an inductive block is being checked; it has a new identity, so no
    evidence derived in it is accepted by the environment it extends, and it can never be committed.
*)

val assume : t -> Decl.t -> unit
(** Add a constant that is assumed, on an overlay only. *)

val add_unsafe : t -> Name.t -> Name.t list -> Evidence.Is_type.t -> unit
(** Record an unsafe or partial declaration. Safe declarations can never mention it ({!Tc}); its
    value is not read. *)

val add_axiom : t -> Name.t -> Name.t list -> Evidence.Is_type.t -> unit

val add_def :
  t ->
  Name.t ->
  Name.t list ->
  hints:Decl.hints ->
  ty:Evidence.Is_type.t ->
  value:Evidence.Typing.t ->
  conv:Evidence.Conv.t ->
  unit

val add_opaque :
  t ->
  Name.t ->
  Name.t list ->
  ty:Evidence.Is_type.t ->
  value:Evidence.Typing.t ->
  conv:Evidence.Conv.t ->
  unit

val add_thm :
  t ->
  Name.t ->
  Name.t list ->
  ty:Evidence.Is_type.t ->
  prop:Evidence.Is_prop.t ->
  value:Evidence.Typing.t ->
  conv:Evidence.Conv.t ->
  unit

val add_inductive : t -> Evidence.Ind_ok.t -> unit
val add_quot : t -> Evidence.Quot_ok.t -> unit
