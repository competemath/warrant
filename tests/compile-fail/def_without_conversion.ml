(* expect: This expression has type *)
let f env n (ty : Warrant.Evidence.Is_type.t) (value : Warrant.Evidence.Typing.t) : unit =
  Warrant.Env.add_def env n [] ~hints:Warrant.Decl.Abbrev ~ty ~value
