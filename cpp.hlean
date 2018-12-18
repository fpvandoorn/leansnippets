import core hit.colimit hit.trunc homotopy.connectedness

open eq is_trunc unit quotient seq_colim pi nat equiv sum is_conn

/-
  This is the formalization which is part of the paper
    Constructing the Propositional Truncation using non-recursive HITs
  submitted to CPP 2016.
-/

/-
  Call a function f weakly constant if (Πa a', f a = f a')
  This theorem states that if f is weakly constant, then (ap f) is weakly constant.
-/
  definition weakly_constant_ap {A B : Type} {f : A → B} {a a' : A} (p q : a = a')
    (H : Π(a a' : A), f a = f a') : ap f p = ap f q :=
  have L : Π{b c : A} {r : b = c}, (H a b)⁻¹ ⬝ H a c = ap f r, from
    (λb c r, eq.rec_on r !con.left_inv),
  L⁻¹ ⬝ L

/- definition of "one step truncation" in terms of quotients -/

namespace one_step_tr
section
  parameters {A : Type}
  variables (a a' : A)

  protected definition R (a a' : A) : Type₀ := unit
  parameter (A)
  definition one_step_tr : Type := quotient R
  parameter {A}
  definition tr : one_step_tr :=
  class_of R a

  definition tr_eq : tr a = tr a' :=
  eq_of_rel _ star

  protected definition rec {P : one_step_tr → Type} (Pt : Π(a : A), P (tr a))
    (Pe : Π(a a' : A), Pt a =[tr_eq a a'] Pt a') (x : one_step_tr) : P x :=
  begin
    fapply (quotient.rec_on x),
    { intro a, apply Pt},
    { intro a a' H, cases H, apply Pe}
  end

  protected definition rec_on [reducible] {P : one_step_tr → Type} (x : one_step_tr)
    (Pt : Π(a : A), P (tr a)) (Pe : Π(a a' : A), Pt a =[tr_eq a a'] Pt a') : P x :=
  rec Pt Pe x

  protected definition elim {P : Type} (Pt : A → P)
    (Pe : Π(a a' : A), Pt a = Pt a') (x : one_step_tr) : P :=
  rec Pt (λa a', pathover_of_eq _ (Pe a a')) x

  protected definition elim_on [reducible] {P : Type} (x : one_step_tr) (Pt : A → P)
    (Pe : Π(a a' : A), Pt a = Pt a') : P :=
  elim Pt Pe x

  theorem rec_tr_eq {P : one_step_tr → Type} (Pt : Π(a : A), P (tr a))
    (Pe : Π(a a' : A), Pt a =[tr_eq a a'] Pt a') (a a' : A)
    : apd (rec Pt Pe) (tr_eq a a') = Pe a a' :=
  !rec_eq_of_rel

  theorem elim_tr_eq {P : Type} (Pt : A → P)
    (Pe : Π(a a' : A), Pt a = Pt a') (a a' : A)
    : ap (elim Pt Pe) (tr_eq a a') = Pe a a' :=
  begin
    apply inj_inv !(pathover_constant (tr_eq a a')),
    rewrite [▸*,-apd_eq_pathover_of_eq_ap,↑elim,rec_tr_eq],
  end

end

definition n_step_tr [reducible] (A : Type) (n : ℕ) : Type :=
nat.rec_on n A (λn' A', one_step_tr A')

end one_step_tr
attribute one_step_tr.rec one_step_tr.elim [recursor 5] [unfold 5]
attribute one_step_tr.rec_on one_step_tr.elim_on [unfold 2]
attribute one_step_tr.tr [constructor]
open one_step_tr

section /- Theorems about the one-step truncation -/
  open homotopy trunc prod
  theorem tr_eq_ne_idp {A : Type} (a : A) : tr_eq a a ≠ idp :=
  begin
    intro p,
    have H2 : Π{X : Type₁} {x : X} {q : x = x}, q = idp,
      from λX x q, calc
        q   = ap (one_step_tr.elim (λa, x) (λa b, q)) (tr_eq a a)               : elim_tr_eq
        ... = ap (one_step_tr.elim (λa, x) (λa b, q)) (refl (one_step_tr.tr a)) : by rewrite p
        ... = idp                                                               : idp,
    exact bool.eq_bnot_ne_idp H2
  end

  theorem tr_eq_ne_ap_tr {A : Type} {a b : A} (p : a = b) : tr_eq a b ≠ ap tr p :=
  by induction p; apply tr_eq_ne_idp

  theorem not_inhabited_set_trunc_one_step_tr (A : Type)
    : ¬(trunc 1 (one_step_tr A) × is_set (trunc 1 (one_step_tr A))) :=
  begin
    intro H, induction H with x H,
    refine trunc.elim_on x _, clear x, intro x,
    induction x,
    { have q : trunc -1 ((tr_eq a a) = idp),
      begin
        refine to_fun !tr_eq_tr_equiv _,
        refine @is_prop.elim _ _ _ _, apply is_trunc_equiv_closed, apply tr_eq_tr_equiv
      end,
      refine trunc.elim_on q _, clear q, intro p, exact !tr_eq_ne_idp p},
    { apply is_prop.elim}
  end

  theorem not_is_conn_one_step_tr (A : Type) : ¬is_conn 1 (one_step_tr A) :=
  λH, not_inhabited_set_trunc_one_step_tr A (!center, _)

  theorem is_prop_trunc_one_step_tr (A : Type) : is_prop (trunc 0 (one_step_tr A)) :=
  begin
    apply is_prop.mk,
    intro x y,
    refine trunc.rec_on x _, refine trunc.rec_on y _, clear x y, intro y x,
    induction x,
    { induction y,
      { exact ap trunc.tr !tr_eq},
      { apply is_prop.elimo}},
    { apply is_prop.elimo}
  end

  local attribute is_prop_trunc_one_step_tr [instance]

  theorem trunc_0_one_step_tr_equiv (A : Type) : trunc 0 (one_step_tr A) ≃ ∥ A ∥ :=
  begin
    apply equiv_of_is_prop,
    { intro x, refine trunc.rec _ x, clear x, intro x, induction x,
      { exact tr a},
      { apply is_prop.elim}},
    { intro x, refine trunc.rec _ x, clear x, intro a, exact tr (tr a)},
  end

  definition one_step_tr_functor [unfold 4] {A B : Type} (f : A → B) (x : one_step_tr A)
    : one_step_tr B :=
  begin
    induction x,
    { exact tr (f a)},
    { apply tr_eq}
  end

  definition one_step_tr_universal_property [constructor] (A B : Type)
    : (one_step_tr A → B) ≃ Σ(f : A → B), Π(x y : A), f x = f y :=
  begin
    fapply equiv.MK,
    { intro f, fconstructor, intro a, exact f (tr a), intros, exact ap f !tr_eq},
    { intro v a, induction v with f p, induction a, exact f a, apply p},
    { intro v, induction v with f p, esimp, apply ap (sigma.mk _), apply eq_of_homotopy2,
      intro a a', apply elim_tr_eq},
    { intro f, esimp, apply eq_of_homotopy, intro a, induction a,
        reflexivity,
        apply eq_pathover, apply hdeg_square, rewrite [▸*,elim_tr_eq]},
  end


end

section
  parameter {X : Type}

  /- basic constructors -/
  private definition A [reducible] (n : ℕ) : Type := nat.rec_on n X (λn' X', one_step_tr X')
  private definition f [reducible] ⦃n : ℕ⦄ (a : A n) : A (succ n)         := tr a
  private definition f_eq [reducible] {n : ℕ} (a a' : A n) : f a = f a'   := tr_eq a a'
  private definition truncX [reducible] : Type                            := @seq_colim A f
  private definition i [reducible] {n : ℕ} (a : A n) : truncX             := inclusion f a
  private definition g [reducible] {n : ℕ} (a : A n) : i (f a) = i a      := glue f a

  /- defining the normal recursor is easy -/
  definition rec {P : truncX → Type} [Pt : Πx, is_prop (P x)]
    (H : Π(a : X), P (@i 0 a)) (x : truncX) : P x :=
  begin
    induction x,
    { induction n with n IH,
      { exact H a},
      { induction a,
        { exact !g⁻¹ ▸ IH a},
        { apply is_prop.elimo}}},
    { apply is_prop.elimo}
  end

  /- point operations -/

  definition fr [reducible] [unfold 2] (n : ℕ) (a : X) : A n :=
  begin
    induction n with n x,
    { exact a},
    { exact f x},
  end

  /- path operations -/

  definition i_fr [unfold 2] (n : ℕ) (a : X) : i (fr n a) = @i 0 a :=
  begin
    induction n with n p,
    { reflexivity},
    { exact g (fr n a) ⬝ p},
  end

  definition eq_same {n : ℕ} (a a' : A n) : i a = i a' :=
  calc
    i a = i (f a)  : g
    ... = i (f a') : ap i (f_eq a a')
    ... = i a'     : g

  definition eq_constructors {n : ℕ} (a : X) (b : A n) : @i 0 a = i b :=
  calc
    i a = i (fr n a) : i_fr
    ... = i b        : eq_same

  /- 2-dimensional path operations -/

  theorem ap_i_ap_f {n : ℕ} {a a' : A n} (p : a = a') : !g⁻¹ ⬝ ap i (ap !f p) ⬝ !g = ap i p :=
  by induction p; apply con.left_inv

  theorem ap_i_eq_ap_i_same {n : ℕ} {a a' : A n} (p q : a = a') : ap i p = ap i q :=
  !weakly_constant_ap eq_same

  theorem ap_f_eq_f {n : ℕ} (a a' : A n)
    : !g⁻¹ ⬝ ap i (f_eq (f a) (f a')) ⬝ !g = ap i (f_eq a a') :=
  ap _ !ap_i_eq_ap_i_same ⬝ !ap_i_ap_f

  theorem eq_same_f {n : ℕ} (a a' : A n)
    : (g a)⁻¹ ⬝ eq_same (f a) (f a') ⬝ g a' = eq_same a a' :=
  begin
   esimp [eq_same],
   apply (ap (λx, _ ⬝ x ⬝ _)),
   apply (ap_f_eq_f a a'),
  end

  theorem eq_constructors_comp {n : ℕ} (a : X) (b : A n)
    : eq_constructors a (f b) ⬝ g b  = eq_constructors a b :=
  begin
    rewrite [↑eq_constructors,▸*,↓fr n a,↓i_fr n a,con_inv,+con.assoc],
    apply ap (λx, _ ⬝ x),
    rewrite -con.assoc, exact !eq_same_f
  end

  theorem is_prop_truncX : is_prop truncX :=
  begin
    apply is_prop_of_imp_is_contr,
    intro a,
    refine @rec _ _ _ a,
    clear a, intro a,
    fapply is_contr.mk,
    exact @i 0 a,
    intro b,
    induction b with n b n b,
    { apply eq_constructors},
    { apply (equiv.to_inv !eq_pathover_equiv_r), apply eq_constructors_comp}
  end

end

namespace my_trunc
  definition trunc.{u} (A : Type.{u}) : Type.{u}                        := @truncX A
  definition tr {A : Type} : A → trunc A                                := @i A 0
  definition is_prop_trunc (A : Type) : is_prop (trunc A)               := is_prop_truncX
  definition trunc.rec {A : Type} {P : trunc A → Type}
    [Pt : Π(x : trunc A), is_prop (P x)]
    (H : Π(a : A), P (tr a)) : Π(x : trunc A), P x                      := @rec A P Pt H

  example {A : Type} {P : trunc A → Type} [Pt : Πaa, is_prop (P aa)]
          (H : Πa, P (tr a)) (a : A) : (trunc.rec H) (tr a) = H a       := by reflexivity

  open sigma prod

  -- the constructed truncation is equivalent to the "standard" propositional truncation
  -- (called _root_.trunc -1 below)
  open trunc
  attribute is_prop_trunc [instance]
  definition trunc_equiv (A : Type) : trunc A ≃ _root_.trunc -1 A :=
  begin
    fapply equiv.MK,
    { intro x, induction x using trunc.rec with a, exact trunc.tr a},
    { intro x, refine _root_.trunc.rec _ x, intro a, exact tr a},
    { intro x, induction x with a, reflexivity},
    { intro x, induction x using trunc.rec with a, reflexivity}
  end

  -- some other recursors we get from this construction:
  definition trunc.elim2 {A P : Type} (h : Π{n}, n_step_tr A n → P)
    (coh : Π(n : ℕ) (a : n_step_tr A n), h (f a) = h a) (x : trunc A) : P :=
  begin
    induction x,
    { exact h a},
    { apply coh}
  end

  definition trunc.rec2 {A : Type} {P : truncX → Type} (h : Π{n} (a : n_step_tr A n), P (i a))
    (coh : Π(n : ℕ) (a : n_step_tr A n), h (f a) =[g a] h a)
    (x : trunc A) : P x :=
  begin
    induction x,
    { exact h a},
    { apply coh}
  end

  definition elim2_equiv [constructor] (A P : Type) : (trunc A → P) ≃
    Σ(h : Π{n}, n_step_tr A n → P),
      Π(n : ℕ) (a : n_step_tr A n), @h (succ n) (one_step_tr.tr a) = h a :=
  begin
    fapply equiv.MK,
    { intro h, fconstructor,
      { intro n a, refine h (i a)},
      { intro n a, exact ap h (g a)}},
    { intro x a, induction x with h p, induction a,
        exact h a,
        apply p},
    { intro x, induction x with h p, fapply sigma_eq,
      { reflexivity},
      { esimp, apply pathover_idp_of_eq, apply eq_of_homotopy2, intro n a, xrewrite elim_glue}},
    { intro h, apply eq_of_homotopy, intro a, esimp, induction a,
        esimp,
        apply eq_pathover, apply hdeg_square, esimp, rewrite elim_glue}
  end

  open sigma.ops
  definition conditionally_constant_equiv {A P : Type} (k : A → P) :
    (Σ(g : trunc A → P), Πa, g (tr a) = k a) ≃
      Σ(h : Π{n}, n_step_tr A n → P),
        (Π(n : ℕ) (a : n_step_tr A n), h (f a) = h a) × (Πa, @h 0 a = k a) :=
  calc
    (Σ(g : trunc A → P), Πa, g (tr a) = k a)
      ≃ Σ(v : Σ(h : Π{n}, n_step_tr A n → P), Π(n : ℕ) (a : n_step_tr A n), h (f a) = h a),
          Πa, (v.1) 0 a = k a
                    : sigma_equiv_sigma !elim2_equiv (λg, equiv.rfl)
  ... ≃ Σ(h : Π{n}, n_step_tr A n → P) (p : Π(n : ℕ) (a : n_step_tr A n), h (f a) = h a),
          Πa, @h 0 a = k a
                    : sigma_assoc_equiv
  ... ≃ Σ(h : Π{n}, n_step_tr A n → P),
          (Π(n : ℕ) (a : n_step_tr A n), h (f a) = h a) × (Πa, @h 0 a = k a)
                    : sigma_equiv_sigma_right (λa, !equiv_prod)

  definition cocone_of_is_collapsible {A : Type} (f : A → A) (p : Πa a', f a = f a')
    (n : ℕ) (x : n_step_tr A n) : A :=
  begin
    apply f,
    induction n with n h,
    { exact x},
    { apply to_inv !one_step_tr_universal_property ⟨f, p⟩, exact one_step_tr_functor h x}
  end

  definition has_split_support_of_is_collapsible {A : Type} (f : A → A) (p : Πa a', f a = f a')
    : trunc A → A :=
  begin
    fapply to_inv !elim2_equiv,
    fconstructor,
    { exact cocone_of_is_collapsible f p},
    { intro n a, apply p}

  end

end my_trunc
