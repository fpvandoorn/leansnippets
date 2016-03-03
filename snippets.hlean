import homotopy.circle types.nat.hott types.pointed cubical.cubeover

/---------------------------------------------------------------------------------------------------
  Show that type quotient preserves equivalence.
  Can this be done without univalence?
---------------------------------------------------------------------------------------------------/
namespace quotient
  open equiv
  universe variables u v
  variables {A B : Type.{u}} {R : A → A → Type.{v}} {S : B → B → Type.{v}}

  definition quotient_equiv (f : A ≃ B) (g : Π(a a' : A), R a a' ≃ S (f a) (f a'))
    : quotient R ≃ quotient S :=
  begin
    revert S g, eapply (equiv.rec_on_ua_idp f), esimp, intro S g,
    have H : R = S,
      by intros, apply eq_of_homotopy, intro a, apply eq_of_homotopy, intro a',
         eapply (equiv.rec_on_ua_idp (g a a')), reflexivity,
    cases H, reflexivity
  end
end quotient

/---------------------------------------------------------------------------------------------------
  Test of pushouts: show that the pushout of the diagram
    1 <- 0 -> 1
  is equivalent to 2.
---------------------------------------------------------------------------------------------------/
namespace pushout
  open equiv is_equiv unit bool
  private definition unit_of_empty (u : empty) : unit := star

  example : pushout unit_of_empty unit_of_empty ≃ bool :=
  begin
    fapply equiv.MK,
    { intro x, induction x with u u c,
        exact ff,
        exact tt,
        cases c},
    { intro b, cases b,
        exact (!inl ⋆),
        exact (!inr ⋆)},
    { intro b, cases b,
        reflexivity,
        reflexivity},
    { intro x, induction x with u u c,
        cases u, reflexivity,
        cases u, reflexivity,
        cases c},
  end

end pushout

/---------------------------------------------------------------------------------------------------
  (Part of) encode-decode proof to characterize the equality type of the natural numbers.
  This is not needed in the library, since we use Hedberg's Theorem to show that the natural numbers
  is a set
---------------------------------------------------------------------------------------------------/
namespace nathide
  open unit eq is_trunc nat
  protected definition code (n m : ℕ) : Type₀ :=
  begin
    revert m,
    induction n with n IH,
    { intro m, cases m,
      { exact unit},
      { exact empty}},
    { intro m, cases m with m,
      { exact empty},
      { exact IH m}},
  end

  protected definition encode {n m : ℕ} (p : n = m) : nat.code n m :=
  begin
    revert m p,
    induction n with n IH,
    { intro m p, cases m,
      { exact star},
      { contradiction}},
    { intro m p, cases m with m,
      { contradiction},
      { rewrite [↑nat.code], apply IH, injection p, assumption}},
  end

  protected definition decode {n m : ℕ} (q : nat.code n m) : n = m :=
  begin
    revert m q,
    induction n with n IH,
    { intro m q, cases m,
      { reflexivity},
      { contradiction}},
    { intro m q, cases m with m,
      { contradiction},
      { exact ap succ (!IH q)}},
  end

  definition is_prop_code (n m : ℕ) : is_prop (nat.code n m) :=
  begin
    apply is_prop.mk, revert m,
    induction n with n IH,
    { intro m p q, cases m,
      { cases p, cases q, reflexivity},
      { contradiction}},
    { intro m p q, cases m with m,
      { contradiction},
      { exact IH m p q}},
  end
  local attribute is_prop_code [instance]
end nathide

/---------------------------------------------------------------------------------------------------
  (Part of) encode-decode proof to characterize < on nat, to show that it is a mere proposition.
  In types.nat.hott there is a simpler proof
---------------------------------------------------------------------------------------------------/

namespace nat
namespace lt
  open unit is_trunc algebra
  protected definition code (n m : ℕ) : Type₀ :=
  begin
    revert m,
    induction n with n IH,
    { intro m, cases m,
      { exact empty},
      { exact unit}},
    { intro m, cases m with m,
      { exact empty},
      { exact IH m}},
  end

  protected definition encode {n m : ℕ} (p : n < m) : lt.code n m :=
  begin
    revert m p,
    induction n with n IH,
    { intro m p, cases m,
      { exfalso, exact !lt.irrefl p},
      { exact star}},
    { intro m p, cases m with m,
      { exfalso, apply !not_lt_zero p},
      { rewrite [↑lt.code], apply IH, apply lt_of_succ_lt_succ p}},
  end

  protected definition decode {n m : ℕ} (q : lt.code n m) : n < m :=
  begin
    revert m q,
    induction n with n IH,
    { intro m q, cases m,
      { contradiction},
      { apply zero_lt_succ}},
    { intro m q, cases m with m,
      { contradiction},
      { exact succ_lt_succ (!IH q)}},
  end

  definition is_prop_code (n m : ℕ) : is_prop (lt.code n m) :=
  begin
    apply is_prop.mk, revert m,
    induction n with n IH,
    { intro m p q, cases m,
      { contradiction},
      { cases p, cases q, reflexivity}},
    { intro m p q, cases m with m,
      { contradiction},
      { exact IH m p q}},
  end
  local attribute is_prop_code [instance]

end lt
end nat

/---------------------------------------------------------------------------------------------------
  Alternative recursor for inequality on ℕ
---------------------------------------------------------------------------------------------------/

namespace nat
  open eq is_trunc


  inductive le2 : ℕ → ℕ → Type :=
  | zero_le2 : Πk, le2 0 k
  | succ_le2_succ : Π{n k : ℕ}, le2 n k → le2 (succ n) (succ k)

  open le2

  definition le2_of_le {n m : ℕ} (H : n ≤ m) : le2 n m :=
  begin
    induction H with m H IH,
    { induction n with n IH,
      { exact zero_le2 0},
      { exact succ_le2_succ IH}},
    { clear H, induction IH with m n m IH IH2,
      { apply zero_le2},
      { exact succ_le2_succ IH2}}
  end

  definition le_of_le2 {n m : ℕ} (H : le2 n m) : n ≤ m :=
  begin
    induction H with m n m H IH,
    { apply zero_le},
    { apply succ_le_succ IH}
  end

  definition nat.le.rec2 {C : Π (n k : ℕ), n ≤ k → Type}
    (H1 : Πk, C 0 k (zero_le k))
    (H2 : (Π{n k : ℕ} (H : n ≤ k), C n k H → C (succ n) (succ k) (succ_le_succ H)))
    {n k : ℕ} (H : n ≤ k) : C n k H :=
  begin
    assert lem : Π(x : le2 n k), C n k (le_of_le2 x),
    { intro x, clear H,
      induction x with k n k x IH,
      { refine transport (C _ _) _ (H1 k), apply is_prop.elim},
      { refine transport (C _ _) _ (H2 (le_of_le2 x) IH), apply is_prop.elim}},
    refine transport (C _ _) _ (lem (le2_of_le H)), apply is_prop.elim
  end

end nat

/---------------------------------------------------------------------------------------------------
  [WIP] Try to see whether having a list of paths is useful
---------------------------------------------------------------------------------------------------/

namespace lpath
  open nat eq
  inductive lpath {A : Type} (a : A) : A → ℕ → Type :=
  lidp : lpath a a 0,
  cons : Π{n : ℕ} {b c : A} (p : b = c) (l : lpath a b n), lpath a c (succ n)

  open lpath.lpath

  protected definition elim {A : Type} : Π{a b : A} {n : ℕ} (l : lpath a b n), a = b
  | elim (lidp a) := idp
  | elim (cons p l) := elim l ⬝ p
end lpath

/---------------------------------------------------------------------------------------------------
  apn is weakly constant
---------------------------------------------------------------------------------------------------/

namespace apn
  open eq pointed nat

  definition weakly_constant_apn {A B : pType} {n : ℕ} {f : map₊ A B} (p : Ω[n] A)
    (H : Π(a : A), f a = pt) : apn n f p = pt :=
  begin
    induction n with n IH,
    { unfold [apn, iterated_ploop_space] at *, apply H},
    { exact sorry}
  end

end apn

/---------------------------------------------------------------------------------------------------
  two quotient eliminator is unique
---------------------------------------------------------------------------------------------------/

/---------------------------------------------------------------------------------------------------
  unit relation on circle
---------------------------------------------------------------------------------------------------/

namespace circlerel
  open circle equiv prod eq
  variables {A : Type} (a : A)
  inductive R : A → A → Type :=
  | Rmk : R a a
  open R

  definition R_equiv (x y) : R a x y ≃ a = x × a = y :=
  begin
    fapply equiv.MK,
    { intro r, induction r, exact (idp, idp)},
    { intro v, induction v with p₁ p₂, induction p₁, induction p₂, exact Rmk a},
    { intro v, induction v with p₁ p₂, induction p₁, induction p₂, reflexivity},
    { intro r, induction r, reflexivity}
  end

  definition R_circle : R base base base ≃ ℤ × ℤ :=
  !R_equiv ⬝e prod_equiv_prod base_eq_base_equiv base_eq_base_equiv

end circlerel

/---------------------------------------------------------------------------------------------------
  Quotienting A with the diagonal relation (smallest reflexive relation) gives A × S¹
---------------------------------------------------------------------------------------------------/

namespace circle

  open eq circle prod quotient equiv

  section
  parameter {A : Type}

  inductive reflexive_rel : A → A → Type :=
  | Rmk : Πx, reflexive_rel x x
  open reflexive_rel

  definition times_circle := quotient reflexive_rel

  definition φ [unfold 2] (x : times_circle) : A × S¹ :=
  begin
    induction x,
    { exact (a, base)},
    { induction H, exact ap (pair x) loop}
  end

  definition ψ [unfold 2] (x : A × S¹) : times_circle :=
  begin
    induction x with x y, induction y,
    { exact class_of _ x},
    { apply eq_of_rel, exact Rmk x}
  end

  definition times_circle_equiv [constructor] : times_circle ≃ A × S¹ :=
  begin
    fapply equiv.MK,
    { exact φ},
    { exact ψ},
    { intro x, induction x with x y, induction y,
      { reflexivity},
      { apply eq_pathover, apply hdeg_square,
        rewrite [ap_compose φ (λa, ψ (x, a)), ▸*, elim_loop, ↑φ], apply elim_eq_of_rel}},
    { intro x, induction x,
      { reflexivity},
      { apply eq_pathover, apply hdeg_square, rewrite [ap_id], refine ap_compose ψ φ _ ⬝ _,
        refine ap (ap ψ) !elim_eq_of_rel ⬝ _, induction H, esimp,
        refine !ap_compose⁻¹ ⬝ _, esimp [function.compose], apply elim_loop}}
  end

  /- the same construction, where the relation is equivalent, but defined differently -/

  definition reflexive_rel2 := @eq A

  definition times_circle2 := quotient reflexive_rel2

  definition φ' [unfold 2] (x : times_circle2) : A × S¹ :=
  begin
    induction x,
    { exact (a, base)},
    { induction H, exact ap (pair a) loop}
  end

  definition ψ' [unfold 2] (x : A × S¹) : times_circle2 :=
  begin
    induction x with x y, induction y,
    { exact class_of _ x},
    { apply eq_of_rel, apply idp}
  end

  definition times_circle2_equiv [constructor] : times_circle2 ≃ A × S¹ :=
  begin
    fapply equiv.MK,
    { exact φ'},
    { exact ψ'},
    { intro x, induction x with x y, induction y,
      { reflexivity},
      { apply eq_pathover, apply hdeg_square,
        rewrite [ap_compose φ' (λa, ψ' (x, a)), ▸*, elim_loop, ↑φ'], apply elim_eq_of_rel}},
    { intro x, induction x,
      { reflexivity},
      { apply eq_pathover, apply hdeg_square, rewrite [ap_id], refine ap_compose ψ' φ' _ ⬝ _,
        refine ap (ap ψ') !elim_eq_of_rel ⬝ _, induction H, esimp,
        refine !ap_compose⁻¹ ⬝ _, esimp [function.compose], apply elim_loop}}
  end

  end

end circle



/---------------------------------------------------------------------------------------------------
  define dependent computation rule of the circle from the other data?
---------------------------------------------------------------------------------------------------/
exit
namespace circlecomp
  section
  open circle eq sigma sigma.ops function equiv

  parameters {P : circle → Type} (Pbase : P base) (Ploop : Pbase =[loop] Pbase)
  include Ploop

  definition eq2_pr1 {A : Type} {B : A → Type} {u v : Σa, B a} {p q : u = v} (r : p = q)
    : p..1 = q..1 :=
  ap eq_pr1 r

  definition eq2_pr2 {A : Type} {B : A → Type} {u v : Σa, B a} {p q : u = v} (r : p = q)
    : p..2 =[eq2_pr1 r] q..2 :=
  !pathover_ap (apdo eq_pr2 r)

  definition natural_square_tr_loop {A : Type} {B : Type} {a : A} {f g : A → B}
    (p : f ~ g) (q : a = a) : natural_square_tr p q = _ :=
  _

  definition pathover_ap_id {A : Type} {a a₂ : A} (B : A → Type) {p : a = a₂}
    {b : B a} {b₂ : B a₂} (q : b =[p] b₂) : pathover_ap B id q = change_path (ap_id p)⁻¹ q :=
  by induction q; reflexivity

  definition pathover_ap_compose {A A' A'' : Type} {a a₂ : A} (B : A'' → Type)
    (g : A' → A'') (f : A → A') {p : a = a₂} {b : B (g (f a))} {b₂ : B (g (f a₂))}
    (q : b =[p] b₂) : pathover_ap B (g ∘ f) q
    = change_path (ap_compose g f p)⁻¹ (pathover_ap B g (pathover_ap (B ∘ g) f q)) :=
  by induction q; reflexivity

  definition pathover_ap_compose_rev {A A' A'' : Type} {a a₂ : A} (B : A'' → Type)
    (g : A' → A'') (f : A → A') {p : a = a₂} {b : B (g (f a))} {b₂ : B (g (f a₂))}
    (q : b =[p] b₂) : pathover_ap B g (pathover_ap (B ∘ g) f q)
    = change_path (ap_compose g f p) (pathover_ap B (g ∘ f) q) :=
  by induction q; reflexivity

  definition f : S¹ → sigma P := circle.elim ⟨base, Pbase⟩ (sigma_eq loop Ploop)
  definition g : Πx, P x := circle.rec Pbase Ploop

  definition foo1 (x : S¹) : (f x).1 = x :=
  circle.rec_on x idp
  begin apply eq_pathover, apply hdeg_square,
    rewrite [ap_id, ap_compose pr1 f,↑f,elim_loop], apply sigma_eq_pr1 end


  definition apdo_eq_apdo_ap {A B : Type} {C : B → Type} (g : Πb, C b) (f : A → B) {a a' : A}
    (p : a = a') : apdo (λx, g (f x)) p = pathover_of_pathover_ap C f (apdo g (ap f p)) :=
  by induction p; reflexivity

  definition foo2 (x : S¹) : (f x).2 =[foo1 x] g x :=
  circle.rec_on x idpo
  begin
    apply pathover_pathover, esimp, --rewrite pathover_ap_id,
    apply transport (λx, squareover P x _ _ _ _),
    apply to_left_inv !hdeg_square_equiv, esimp,
    apply hdeg_squareover,
    rewrite [pathover_ap_id, apdo_eq_apdo_ap pr2 f loop, ]
    --unfold natural_square_tr,
  end

  definition p : ap f loop = (sigma_eq loop Ploop) := !elim_loop
  definition q : (ap f loop)..1 = loop := ap eq_pr1 p ⬝ !sigma_eq_pr1
  definition r : (ap f loop)..2 =[q] Ploop :=
  !eq2_pr2 ⬝o !sigma_eq_pr2

--set_option pp.notation false
  theorem my_rec_loop  : apdo (circle.rec Pbase Ploop) loop = Ploop :=
  begin
    refine _ ⬝ tr_eq_of_pathover r,
  end

  end
end circlecomp

  /- try to use the circle to transport the computation rule from the circle to the new type -/
namespace circlecomp2

  open circle eq sigma sigma.ops function equiv is_equiv

  definition X : Type₀ := circle
  definition b : X := base
  definition l : b = b := loop
  definition elim {C : Type} (c : C) (p : c = c) (x : X) : C := circle.elim c p x
  definition rec {C : X → Type} (c : C b) (p : c =[l] c) (x : X) : C x := circle.rec c p x
  theorem elim_l {C : Type} (c : C) (p : c = c) : ap (elim c p) l = p := elim_loop c p

  attribute X l [irreducible]
  attribute rec elim [unfold 4] [recursor 4]
  attribute b [constructor]

  example {C : Type} (c : C) (p : c = c) : elim c p b = c := begin esimp end

  definition XequivS : X ≃ S¹ :=
  begin
    fapply equiv.MK,
    { intro x, induction x, exact base, exact loop},
    { intro y, induction y, exact b, exact l},
    { intro y, induction y, esimp, apply eq_pathover, apply hdeg_square,
      rewrite [ap_id,ap_compose (elim base loop),elim_loop], apply elim_l},
    { intro x, induction x, esimp, apply eq_pathover, apply hdeg_square,
      rewrite [ap_id,ap_compose (circle.elim b l),elim_l], apply elim_loop},
  end

  --set_option pp.notation false
  definition foo {A A' : Type} (f : A ≃ A') (B : A → Type) {a a' : A} {p : a = a'}
    {b : B a} {b' : B a'} : b =[p] b' ≃
  pathover (B ∘ to_inv f) ((to_left_inv f a)⁻¹ ▸ b) (ap (to_fun f) p) ((to_left_inv f a')⁻¹ ▸ b') :=
  begin
    induction p, esimp,
    refine !pathover_idp ⬝e _ ⬝e !pathover_idp⁻¹ᵉ,
    apply eq_equiv_fn_eq
  end

  theorem rec_l {C : X → Type} (c : C b) (p : c =[l] c) : apdo (rec c p) l = p :=
  begin
    refine eq_of_fn_eq_fn !(foo XequivS) _,
  end
end circlecomp2
