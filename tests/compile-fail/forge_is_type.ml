(* expect: private *)
let _ =
  {
    Warrant.Evidence.Is_type.env = 0;
    lparams = [];
    e = Warrant.Expr.bvar 0;
    level = Warrant.Level.zero;
  }
