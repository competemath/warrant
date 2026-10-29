(** Kernel terms: locally nameless, hash-consed, binder names and binder info erased.

    The cached fields ([lbr], [has_fvar], [has_lparam]) are computed by the smart constructors and
    the type is private, so a term whose cache disagrees with its shape cannot be built. Two terms
    are alpha-equivalent iff they are physically equal. *)

type t = private {
  id : int;
  node : node;
  lbr : int;
  has_fvar : bool;
  maxfv : int;
  has_lparam : bool;
}

and node =
  | BVar of int
  | FVar of int
  | Sort of Level.t
  | Const of Name.t * Level.t list
  | App of t * t
  | Lam of t * t
  | Pi of t * t
  | Let of t * t * t
  | Nat of Z.t
  | Str of string
  | Proj of Name.t * int * t

val permanently : (unit -> 'a) -> 'a
(** [permanently f]: terms built while [f] runs are kept for the whole run (the parser uses it for
    the file's terms). *)

val bvar : int -> t
val fvar : int -> t
val sort : Level.t -> t
val const : Name.t -> Level.t list -> t
val app : t -> t -> t
val lam : t -> t -> t
val pi : t -> t -> t
val let_ : t -> t -> t -> t
val nat : Z.t -> t
val str : string -> t
val proj : Name.t -> int -> t -> t
val mk_app : t -> t list -> t
val get_app_fn : t -> t
val get_app_args : t -> t list
val get_app_num_args : t -> int

val for_all_fvars : (int -> bool) -> t -> bool
(** [for_all_fvars p e]: every free variable of [e] satisfies [p]. *)

val instantiate_rev : t -> t array -> t
(** [instantiate_rev e subst] replaces loose [bvar i] ([i < n]) by [subst.(n-1-i)] and lowers the
    others by [n]. *)

val instantiate1 : t -> t -> t

val abstract : t -> int array -> t
(** [abstract e ids] replaces [fvar ids.(k)] by [bvar (n-1-k)] (shifted under binders). *)

val inst_lparams : Name.t list -> Level.t list -> t -> t

val replace : (int -> t -> t option) -> t -> t
(** [replace f e] rebuilds [e] top-down: where [f depth sub] answers, that answer replaces [sub]
    (its children are not visited). *)

val has_loose_bvar : t -> int -> bool

val consts : t -> Name.t list
(** The distinct constants a term mentions, in order of first occurrence. *)

val exists_const : (Name.t -> bool) -> t -> bool
(** Some constant of the term satisfies the predicate. *)

val to_string : t -> string
