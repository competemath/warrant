(* expect: private *)
let _ =
  {
    Warrant.Expr.id = 0;
    node = Warrant.Expr.BVar 0;
    lbr = 0;
    has_fvar = false;
    maxfv = 0;
    has_lparam = false;
  }
