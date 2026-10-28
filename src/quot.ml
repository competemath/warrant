(** The quotient package. The file's [quot] declarations are claims; the four types are rebuilt here
    from [Eq] and compared, [Eq] itself is compared with its expected shape, and each one needs the
    ones it mentions. *)

open Verdict
module E = Expr

let nm = Name.of_dotted
let n_quot = nm "Quot"
let n_mk = nm "Quot.mk"
let n_lift = nm "Quot.lift"
let n_ind = nm "Quot.ind"
let n_eq = nm "Eq"
let n_eq_refl = nm "Eq.refl"
let sort l = E.sort l
let prop = sort Level.zero
let b i = E.bvar i
let ( %@ ) f a = E.app f a

(* the expected shape of Eq: [Eq.{u} : {α : Sort u} → α → α → Prop] with one constructor
   [Eq.refl.{u} : {α : Sort u} → (a : α) → @Eq α a a] *)
let eq_ty lu = E.pi (sort lu) (E.pi (b 0) (E.pi (b 1) prop))
let eq_c lu = E.const n_eq [ lu ]
let eq_refl_ty lu = E.pi (sort lu) (E.pi (b 0) (eq_c lu %@ b 1 %@ b 0 %@ b 0))

(* [Eq] is declared with some one universe parameter; its name is immaterial *)
let check_eq env =
  match (Env.find env n_eq, Env.find env n_eq_refl) with
  | Some ({ kind = Decl.Induct i; lparams = [ eu ]; _ } as d), Some ({ kind = Decl.Ctor c; _ } as r)
    ->
      let lu = Level.param eu in
      if
        d.ty != eq_ty lu
        || i.nparams <> 2 || i.nindices <> 1 || i.ctors <> [ n_eq_refl ] || r.lparams <> [ eu ]
        || r.ty != eq_refl_ty lu
        || c.induct != n_eq
      then
        reject "quotient: Eq is not the expected inductive family (%s | %s | %d %d | %s)"
          (E.to_string d.ty) (E.to_string r.ty) i.nparams i.nindices
          (String.concat "," (List.map Name.to_string i.ctors))
  | _ -> reject "quotient: Eq is not declared"

(* α → α → Prop, under the binders in scope: [a] is the de Bruijn index of α when the relation type is built *)
let rel_ty a = E.pi (b a) (E.pi (b (a + 1)) prop)

(* [expected kind lparams]: the canonical name and type, written with the universe parameter names the file chose
   (renaming a universe parameter changes nothing); the number of parameters must be the canonical one *)
let expected (kind : Decl.quot_kind) (lps : Name.t list) =
  let arity = match kind with Decl.QLift -> 2 | _ -> 1 in
  if List.length lps <> arity || (arity = 2 && List.nth lps 0 == List.nth lps 1) then
    reject "quotient: wrong universe parameters";
  let u = List.hd lps in
  let lu = Level.param u in
  let v = if arity = 2 then List.nth lps 1 else u in
  let lv = Level.param v in
  let quot_c = E.const n_quot [ lu ] and mk_c = E.const n_mk [ lu ] in
  let eq_lv_level = lv in
  ignore eq_lv_level;
  match kind with
  | Decl.QType -> (n_quot, E.pi (sort lu) (E.pi (rel_ty 0) (sort lu)))
  | Decl.QCtor ->
      (* {α : Sort u} → (r : α → α → Prop) → α → @Quot α r *)
      (n_mk, E.pi (sort lu) (E.pi (rel_ty 0) (E.pi (b 1) (quot_c %@ b 2 %@ b 1))))
  | Decl.QLift ->
      (* {α : Sort u} → {r : α → α → Prop} → {β : Sort v} → (f : α → β) →
         (∀ a b : α, r a b → @Eq β (f a) (f b)) → @Quot α r → β *)
      let eq_v = E.const n_eq [ lv ] in
      let f_ty = E.pi (b 2) (b 1) in
      (* context: α r β f  -> indices α=3 r=2 β=1 f=0 *)
      let h_ty =
        (* ∀ (a : α) (b : α), r a b → @Eq β (f a) (f b)
           under a: α=4 r=3 β=2 f=1 a=0; under b: α=5 r=4 β=3 f=2 a=1 b=0; under h: α=6 r=5 β=4 f=3 a=2 b=1 *)
        E.pi (b 3)
          (E.pi (b 4) (E.pi (b 4 %@ b 1 %@ b 0) (eq_v %@ b 4 %@ (b 3 %@ b 2) %@ (b 3 %@ b 1))))
      in
      (* after f and h: α=5? context α r β f h: α=4 r=3 β=2 f=1 h=0; the quotient argument: @Quot α r *)
      let q_ty = quot_c %@ b 4 %@ b 3 in
      (* result β under the q binder: α=5 r=4 β=3 f=2 h=1 q=0 *)
      ( n_lift,
        E.pi (sort lu) (E.pi (rel_ty 0) (E.pi (sort lv) (E.pi f_ty (E.pi h_ty (E.pi q_ty (b 3))))))
      )
  | Decl.QInd ->
      (* {α : Sort u} → {r : α → α → Prop} → {β : @Quot α r → Prop} →
         (mk : ∀ a : α, β (@Quot.mk α r a)) → ∀ q : @Quot α r, β q *)
      let beta_ty = E.pi (quot_c %@ b 1 %@ b 0) prop in
      (* context α r β: α=2 r=1 β=0 ; mk : ∀ a, β (Quot.mk α r a) ; under a: α=3 r=2 β=1 a=0 *)
      let mk_ty = E.pi (b 2) (b 1 %@ (mk_c %@ b 3 %@ b 2 %@ b 0)) in
      (* context α r β mk: α=3 r=2 β=1 mk=0 ; q : @Quot α r ; result β q: under q: β=2 q=0 *)
      let q_ty = quot_c %@ b 3 %@ b 2 in
      (n_ind, E.pi (sort lu) (E.pi (rel_ty 0) (E.pi beta_ty (E.pi mk_ty (E.pi q_ty (b 2 %@ b 0))))))

let admit env (kind : Decl.quot_kind) name lparams ty : Evidence.Quot_ok.t =
  let n, expected_ty = expected kind lparams in
  if name != n then reject "quotient: unexpected name %s" (Name.to_string name);
  if ty != expected_ty then
    reject "quotient: the type of %s is not the expected one" (Name.to_string name);
  check_eq env;
  let need k what =
    match Env.find env k with
    | Some { kind = Decl.Quot _; _ } -> ()
    | _ -> reject "quotient: %s needs %s" (Name.to_string name) what
  in
  (match kind with
  | Decl.QType -> ()
  | Decl.QCtor -> need n_quot "Quot"
  | Decl.QLift ->
      need n_quot "Quot";
      need n_mk "Quot.mk"
  | Decl.QInd ->
      need n_quot "Quot";
      need n_mk "Quot.mk");
  Evidence.Mint.quot_ok ~env:(Env.id env) [ { Decl.name; lparams; ty; kind = Decl.Quot kind } ]
