(* expect: private *)
let _ =
  {
    Warrant.Evidence.Typing.env = 0;
    lparams = [];
    e = Warrant.Expr.bvar 0;
    ty = Warrant.Expr.bvar 0;
  }
