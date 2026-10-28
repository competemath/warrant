(* expect: This expression has type *)
let f env n (ty : Warrant.Evidence.Is_type.t) (value : Warrant.Evidence.Typing.t)
    (conv : Warrant.Evidence.Conv.t) : unit =
  Warrant.Env.add_thm env n [] ~ty ~value ~conv
