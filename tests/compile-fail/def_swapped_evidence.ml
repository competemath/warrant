(* expect: but an expression was expected of type *)
let f env n (ty : Warrant.Evidence.Is_type.t) (value : Warrant.Evidence.Typing.t)
    (conv : Warrant.Evidence.Conv.t) =
  Warrant.Env.add_def env n [] ~hints:Warrant.Decl.Abbrev ~ty:value ~value:ty ~conv
