(** Declarations as the kernel stores them. Every field is either an input the file states about the
    declaration itself (name, universe parameters, type, value) or something the kernel derived;
    nothing here is a claim copied from the file's metadata. *)

type hints = Opaque | Abbrev | Regular of int
type quot_kind = QType | QCtor | QLift | QInd
type rule = { ctor : Name.t; nfields : int; rhs : Expr.t }

type induct = {
  all : Name.t list;
  ctors : Name.t list;
  nparams : int;
  nindices : int;
  is_rec : bool;
  is_reflexive : bool;
  nnested : int;
}

type ctor = { induct : Name.t; cidx : int; cparams : int; nfields : int }

type recursor = {
  rall : Name.t list;
  major_induct : Name.t;  (** the inductive type the recursor eliminates *)
  rparams : int;
  rindices : int;
  nmotives : int;
  nminors : int;
  rules : rule list;
  k : bool;
}

type kind =
  | Axiom
  | Unsafe_const
      (** an unsafe or partial declaration: its type is recorded, its value is neither checked nor
          ever used *)
  | Def of { value : Expr.t; hints : hints }
  | Thm of { value : Expr.t }
  | Opaque_def of { value : Expr.t }
  | Quot of quot_kind
  | Induct of induct
  | Ctor of ctor
  | Rec of recursor

type t = { name : Name.t; lparams : Name.t list; ty : Expr.t; kind : kind }
