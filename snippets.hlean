import homotopy.circle types.nat.basic types.pointed

/---------------------------------------------------------------------------------------------------
  Show that type quotient preserves equivalence.
  Can this be done without univalence?
---------------------------------------------------------------------------------------------------/
namespace quotient
  open equiv.ops equiv
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
namespace nat
  open unit eq is_trunc
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

  definition is_hprop_code (n m : ℕ) : is_hprop (nat.code n m) :=
  begin
    apply is_hprop.mk, revert m,
    induction n with n IH,
    { intro m p q, cases m,
      { cases p, cases q, reflexivity},
      { contradiction}},
    { intro m p q, cases m with m,
      { contradiction},
      { exact IH m p q}},
  end
  local attribute is_hprop_code [instance]
end nat

/---------------------------------------------------------------------------------------------------
  (Part of) encode-decode proof to characterize < on nat, to show that it is a mere proposition.
  In types.nat.hott there is a simpler proof
---------------------------------------------------------------------------------------------------/

namespace nat
namespace lt
  open unit is_trunc
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

  definition is_hprop_code (n m : ℕ) : is_hprop (lt.code n m) :=
  begin
    apply is_hprop.mk, revert m,
    induction n with n IH,
    { intro m p q, cases m,
      { contradiction},
      { cases p, cases q, reflexivity}},
    { intro m p q, cases m with m,
      { contradiction},
      { exact IH m p q}},
  end
  local attribute is_hprop_code [instance]

end lt
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

  definition weakly_constant_apn {A B : Pointed} {n : ℕ} {f : map₊ A B} (p : Ω[n] A)
    (H : Π(a : A), f a = pt) : apn n f p = pt :=
  begin
    induction n with n IH,
    { unfold [apn, Iterated_loop_space] at *, apply H},
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
