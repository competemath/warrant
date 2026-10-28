(* expect: private *)
let _ =
  { Warrant.Evidence.Conv.env = 0; lparams = []; a = Warrant.Expr.bvar 0; b = Warrant.Expr.bvar 1 }
