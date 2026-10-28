(** Hierarchical names, hash-consed: two names are equal iff they are physically equal. *)

type t = private { id : int; node : node }
and node = Anon | Str of t * string | Num of t * int

val anon : t
val str : t -> string -> t
val num : t -> int -> t
val equal : t -> t -> bool
val compare : t -> t -> int
val hash : t -> int
val to_string : t -> string

val of_dotted : string -> t
(** [of_dotted "Nat.rec"] builds [Nat.rec]; for names the kernel itself mentions. *)

val prefix : t -> t

val replace_prefix : t -> t -> t -> t
(** [replace_prefix n old nw]: [n] with its prefix [old] replaced by [nw] (unchanged when [old] is
    not a prefix). *)

val is_prefix_of : t -> t -> bool

module Tbl : Hashtbl.S with type key = t
