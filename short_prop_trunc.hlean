import types.eq types.pi hit.colimit types.nat.hott hit.trunc types.cubical.square types.hprop_trunc

open eq is_trunc unit quotient seq_colim pi nat equiv sum

/-
  Trying a different construction of the propositional truncation
  Original proof length of "is_hprop truncX": 163 lines
  Proof length here: 76 lines
-/


/- HELPER LEMMAS -/

  definition inv_con_con_eq_of_eq_con_con_inv {A : Type} {a₁ a₂ b₁ b₂ : A} {p : a₁ = b₁}
    {q : a₁ = a₂} {r : a₂ = b₂} {s : b₁ = b₂} (H : q = p ⬝ s ⬝ r⁻¹) : p⁻¹ ⬝ q ⬝ r = s :=
  begin
    apply con_eq_of_eq_con_inv,
    apply inv_con_eq_of_eq_con,
    rewrite -con.assoc,
    apply H
  end

/-
  Call a function f weakly constant if Πa a', f a = f a'
  This theorem states that if f is weakly constant, then ap f is weakly constant.
-/
  definition weakly_constant_ap {A B : Type} {f : A → B} {a a' : A} (p q : a = a')
    (H : Π(a a' : A), f a = f a') : ap f p = ap f q :=
  have L : Π{b c : A} {r : b = c}, (H a b)⁻¹ ⬝ H a c = ap f r, from
    (λb c r, eq.rec_on r !con.left_inv),
  L⁻¹ ⬝ L

/- definition of "one step truncation" -/

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

  protected definition elim {P : Type} (Pt : A → P)
    (Pe : Π(a a' : A), Pt a = Pt a') (x : one_step_tr) : P :=
  rec Pt (λa a', pathover_of_eq (Pe a a')) x

  theorem rec_tr_eq {P : one_step_tr → Type} (Pt : Π(a : A), P (tr a))
    (Pe : Π(a a' : A), Pt a =[tr_eq a a'] Pt a') (a a' : A)
    : apdo (rec Pt Pe) (tr_eq a a') = Pe a a' :=
  !rec_eq_of_rel

  theorem elim_tr_eq {P : Type} (Pt : A → P)
    (Pe : Π(a a' : A), Pt a = Pt a') (a a' : A)
    : ap (elim Pt Pe) (tr_eq a a') = Pe a a' :=
  begin
    apply eq_of_fn_eq_fn_inv !(pathover_constant (tr_eq a a')),
    rewrite [▸*,-apdo_eq_pathover_of_eq_ap,↑elim,rec_tr_eq],
  end

end

definition n_step_tr (A : Type) (n : ℕ) : Type := nat.rec_on n A (λn' A', one_step_tr A')
end one_step_tr
attribute one_step_tr.rec one_step_tr.elim [recursor 5]
open one_step_tr

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
  definition rec {P : truncX → Type} [Pt : Πx, is_hprop (P x)]
    (H : Π(a : X), P (@i 0 a)) (x : truncX) : P x :=
  begin
    induction x,
    { induction n with n IH,
      { exact H a},
      { induction a,
        { exact !g⁻¹ ▸ IH a},
        { apply is_hprop.elimo}}},
    { apply is_hprop.elimo}
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

  theorem ap_i_ap_f {n : ℕ} {a a' : A n} (p : a = a') : ap i (ap !f p) = !g ⬝ ap i p ⬝ !g⁻¹ :=
  eq.rec_on p !con.right_inv⁻¹

  theorem ap_i_eq_ap_i_same {n : ℕ} {a a' : A n} (p q : a = a') : ap i p = ap i q :=
  !weakly_constant_ap eq_same

  theorem ap_f_eq_f' {n : ℕ} (a a' : A n)
    : ap i (f_eq (f a) (f a')) = g (f a) ⬝ ap i (f_eq a a') ⬝ (g (f a'))⁻¹ :=
  !ap_i_eq_ap_i_same ⬝ !ap_i_ap_f

  theorem ap_f_eq_f {n : ℕ} (a a' : A n)
    : (g (f a))⁻¹ ⬝ ap i (f_eq (f a) (f a')) ⬝ g (f a') = ap i (f_eq a a') :=
  inv_con_con_eq_of_eq_con_con_inv !ap_f_eq_f'

  theorem eq_same_f {n : ℕ} (a a' : A n)
    : (g a)⁻¹ ⬝ eq_same (f a) (f a') ⬝ g a' = eq_same a a' :=
  begin
   esimp [eq_same],
   apply (ap (λx, _ ⬝ x ⬝ _)),
   apply (ap_f_eq_f a a'),
  end

  definition eq_same_con {n : ℕ} (a : A n) {a' a'' : A n} (p : a' = a'')
    : eq_same a a' = eq_same a a'' ⬝ (ap i p)⁻¹ :=
  by induction p; reflexivity

  -- step (2), n ≤ m
  theorem eq_constructors_comp {n : ℕ} (a : X) (b : A n)
    : eq_constructors a (f b) ⬝ g b  = eq_constructors a b :=
  begin
    rewrite [↑eq_constructors,▸*,↓fr n a,↓i_fr n a,con_inv,+con.assoc],
    apply ap (λx, _ ⬝ x),
    rewrite -con.assoc, exact !eq_same_f
  end

  theorem is_hprop_truncX : is_hprop truncX :=
  begin
    apply is_hprop_of_imp_is_contr,
    intro a,
    refine @rec _ _ _ a,
    clear a, intro a,
    fapply is_contr.mk,
    exact @i 0 a,
    intro b,
    induction b with n b n b,
    { apply eq_constructors},
    { apply (equiv.to_inv !pathover_eq_equiv_r), apply eq_constructors_comp}
  end


end
