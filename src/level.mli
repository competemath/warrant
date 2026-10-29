(** Universe levels, hash-consed, with a semantic decision procedure.

    Comparison of levels is decided over {e every} valuation of the parameters in the naturals (case
    split on the zero-ness of each parameter that occurs under the right-hand side of an [imax],
    then a complete comparison of the resulting max/succ normal forms). There is no syntactic
    approximation and no heuristic fallback: where the procedure would be too expensive it raises
    {!Too_complex}, which the driver turns into a decline. *)

type t = private { id : int; node : node }
and node = Zero | Succ of t | Max of t * t | IMax of t * t | Param of Name.t

val zero : t
val one : t
val succ : t -> t
val max : t -> t -> t
val imax : t -> t -> t
val param : Name.t -> t
val hash : t -> int
val to_string : t -> string

val inst : Name.t list -> t list -> t -> t
(** [inst ps ls l] replaces the parameter [ps.(i)] by [ls.(i)]; the lists have equal length. *)

val params_within : Name.t list -> t -> bool
(** Every parameter of the level is in the given list. *)

exception Too_complex

type leq = private { lhs : t; rhs : t }
(** Evidence that [lhs <= rhs] under every valuation of the parameters. Minted only by {!leq}. *)

val leq : t -> t -> leq option
val equiv : t -> t -> bool

val is_zero : t -> bool
(** The level is 0 under every valuation. *)

val is_never_zero : t -> bool
(** The level is at least 1 under every valuation. *)
