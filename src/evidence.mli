(** Evidence: the only things the checker trusts.

    A fact the kernel acts on (a term is a type, a term has a type, two terms are convertible, a
    type is a proposition, an inductive block is admissible, the quotient package is in place) is a
    value of one of these types. Each carries the identity of the environment it was derived in and
    the universe parameters it holds under. The types are private: the only construction site of
    each is its function in {!Mint}, and [tools/check_minters.py] (run by CI) fails when a mint
    function is referenced from a module other than its designated minter, or called from more than
    one place. Consumers ({!Env}) check the stamps. *)

type env_id = int

module Is_type : sig
  type t = private { env : env_id; lparams : Name.t list; e : Expr.t; level : Level.t; safe : bool }
end

module Typing : sig
  type t = private { env : env_id; lparams : Name.t list; e : Expr.t; ty : Expr.t }
end

module Conv : sig
  type t = private { env : env_id; lparams : Name.t list; a : Expr.t; b : Expr.t }
end

module Is_prop : sig
  type t = private { env : env_id; lparams : Name.t list; e : Expr.t }
end

module Ind_ok : sig
  type t = private { env : env_id; decls : Decl.t list }
end

module Quot_ok : sig
  type t = private { env : env_id; decls : Decl.t list }
end

(** Construction sites. Referenced only from the minters named in [tools/check_minters.py]. *)
module Mint : sig
  val is_type : env:env_id -> lparams:Name.t list -> safe:bool -> Expr.t -> Level.t -> Is_type.t
  val typing : env:env_id -> lparams:Name.t list -> Expr.t -> Expr.t -> Typing.t
  val conv : env:env_id -> lparams:Name.t list -> Expr.t -> Expr.t -> Conv.t
  val is_prop : env:env_id -> lparams:Name.t list -> Expr.t -> Is_prop.t
  val ind_ok : env:env_id -> Decl.t list -> Ind_ok.t
  val quot_ok : env:env_id -> Decl.t list -> Quot_ok.t
end
