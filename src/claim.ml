(** What a file {e says} about an inductive block. Nothing here is trusted: {!Ind} derives every one
    of these fields from the types and constructor types alone and compares. *)

type rule = { ctor : Name.t; nfields : int; rhs : Expr.t }

type ind_type = {
  name : Name.t;
  lparams : Name.t list;
  ty : Expr.t;
  all : Name.t list;
  ctors : Name.t list;
  nparams : int;
  nindices : int;
  is_rec : bool;
  is_reflexive : bool;
  nnested : int;
  unsafe : bool;
}

type ctor = {
  cname : Name.t;
  clparams : Name.t list;
  cty : Expr.t;
  induct : Name.t;
  cidx : int;
  cnparams : int;
  nfields : int;
  cunsafe : bool;
}

type recursor = {
  rname : Name.t;
  rlparams : Name.t list;
  rty : Expr.t;
  rall : Name.t list;
  rnparams : int;
  rnindices : int;
  nmotives : int;
  nminors : int;
  rules : rule list;
  k : bool;
  runsafe : bool;
}

type block = { types : ind_type list; ctor_decls : ctor list; recs : recursor list }
