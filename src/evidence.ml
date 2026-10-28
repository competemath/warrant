type env_id = int

module Is_type = struct
  type t = { env : env_id; lparams : Name.t list; e : Expr.t; level : Level.t; safe : bool }
end

module Typing = struct
  type t = { env : env_id; lparams : Name.t list; e : Expr.t; ty : Expr.t }
end

module Conv = struct
  type t = { env : env_id; lparams : Name.t list; a : Expr.t; b : Expr.t }
end

module Is_prop = struct
  type t = { env : env_id; lparams : Name.t list; e : Expr.t }
end

module Ind_ok = struct
  type t = { env : env_id; decls : Decl.t list }
end

module Quot_ok = struct
  type t = { env : env_id; decls : Decl.t list }
end

module Mint = struct
  let is_type ~env ~lparams ~safe e level : Is_type.t = { env; lparams; e; level; safe }
  let typing ~env ~lparams e ty : Typing.t = { env; lparams; e; ty }
  let conv ~env ~lparams a b : Conv.t = { env; lparams; a; b }
  let is_prop ~env ~lparams e : Is_prop.t = { env; lparams; e }
  let ind_ok ~env decls : Ind_ok.t = { env; decls }
  let quot_ok ~env decls : Quot_ok.t = { env; decls }
end
