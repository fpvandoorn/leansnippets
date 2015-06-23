import types.eq types.pi hit.colimit types.nat.hott hit.sphere

--open unit pi equiv sum
open eq quotient sphere sphere.ops nat sphere_index seq_colim is_trunc sum


-- /- HELPER LEMMAS -/

--   definition inv_con_con_eq_of_eq_con_con_inv {A : Type} {a₁ a₂ b₁ b₂ : A} {p : a₁ = b₁}
--     {q : a₁ = a₂} {r : a₂ = b₂} {s : b₁ = b₂} (H : q = p ⬝ s ⬝ r⁻¹) : p⁻¹ ⬝ q ⬝ r = s :=
--   begin
--     apply con_eq_of_eq_con_inv,
--     apply inv_con_eq_of_eq_con,
--     rewrite -con.assoc,
--     apply H
--   end

-- /-
--   Call a function f weakly constant if Πa a', f a = f a'
--   This theorem states that if f is weakly constant, then ap f is weakly constant.
-- -/
--   definition weakly_constant_ap {A B : Type} {f : A → B} {a a' : A} (p q : a = a')
--     (H : Π(a a' : A), f a = f a') : ap f p = ap f q :=
--   have H' : Π{b c : A} (r : b = c), (H a b)⁻¹ ⬝ H a c = ap f r, from
--     (λb c r, eq.rec_on r !con.left_inv),
--   !H'⁻¹ ⬝ !H'

/- definition of the one step n-truncation -/

namespace dtr
section
  parameters {k : ℕ} {A : Type}

  abbreviation B := A + (S k → A)
  inductive R : B → B → Type :=
  | Rmk : Π(s : S k → A) (x : S k), R (inl (s x)) (inr s)

  definition dtr : Type := quotient R --Make explicit after #652

  definition tr [constructor] (a : A) : dtr :=
  class_of R (inl a)

  definition aux (s : S k → A) : dtr :=
  class_of R (inr s)

  definition tr_eq (s : S k → A) (x : S k) : tr (s x) = aux s :=
  !eq_of_rel !R.Rmk

  protected definition rec [recursor] {P : dtr → Type} (Pt : Π(a : A), P (tr a))
    (Pa : Π(s : S k → A), P (aux s))
    (Pe : Π(s : S k → A) (x : S k), Pt (s x) =[tr_eq s x] Pa s) (x : dtr) : P x :=
  begin
    fapply (quotient.rec_on x),
    { intro a, cases a, apply Pt, apply Pa},
    { intro a a' H, cases H, apply Pe}
  end

end
end dtr
attribute dtr.rec [unfold-c 7]


open dtr

section
  parameters {X : Type} {k : ℕ}

  /- basic constructors -/
  private definition A [reducible] (n : ℕ) : Type := nat.rec_on n X (λn' X', @dtr k X')
  private definition f [reducible] [constructor] ⦃n : ℕ⦄ (a : A n) : A (succ n)        := tr a
  private definition f_eq [reducible] ⦃n : ℕ⦄ (s : S k → A n) (x : S k) : f (s x) = aux s :=
  tr_eq s x
  private definition f_eq2 [reducible] ⦃n : ℕ⦄ (s : S k → A n) (x y : S k) : f (s x) = f (s y) :=
  tr_eq s x ⬝ (tr_eq s y)⁻¹
  private definition my_tr [reducible] : Type                            := @seq_colim A f
  private definition i [reducible] {n : ℕ} (a : A n) : my_tr             := inclusion f a
  private definition g [reducible] {n : ℕ} (a : A n) : i (f a) = i a     := glue f a


  -- defining the recursor
  private definition rec {P : my_tr → Type} [Pt : Πx, is_trunc (k.-2.+1) (P x)]
    (H : Π(a : X), P (@i 0 a)) (x : my_tr) : P x :=
  begin
    induction x,
    { induction n with n IH,
      { exact H a},
      { --▸@dtr k (A n) at a,
        induction a,
        { exact (g a)⁻¹ ▸ IH a},
        { exact f_eq s base ▸ !g⁻¹ ▸ IH (s (base))},
        { apply pathover_of_tr_eq, apply map_sphere_constant_of_is_trunc}}},
    { induction n with n IH; all_goals esimp at *,
      { apply tr_pathover} ,
      { induction a; all_goals esimp at *,
        { clear IH, apply sorry},
        { apply sorry},
        { apply sorry}}


}
  end

exit
--   private definition elim {P : Type} [Pt : is_trunc (k.-2.+1) P]
--     (H : X → P) (x : my_tr) : P :=
--   begin
--     induction x,
--     { induction n with n IH,
--       { exact H a},
--       { rewrite ▸@dtr k (A n) at a,
--         induction a,
--         { exact IH a},
--         { },
--         { apply pathover_of_eq, revert s x, }
-- }},
--     { }
--   end

  /-
    To prove: is_trunc (k-1) my_tr
  -/

  /- point operations -/

  definition fr [reducible] [unfold-c 4] {n m : ℕ} (a : A n) (H : n ≤ m) : A m :=
  begin
    induction H with m H b,
    { exact a},
    { exact f b},
  end

  /- path operations -/

  definition i_fr [unfold-c 4] {n m : ℕ} (a : A n) (H : n ≤ m) : i (fr a H) = i a :=
  begin
    induction H with m H IH,
    { reflexivity},
    { exact g (fr a H) ⬝ IH},
  end

  definition eq_same {n : ℕ} (a a' : A n) : i a = i a' :=
  calc
    i a = i (f a) : g
        ... = i (f a') : ap i (f_eq a a')
        ... = i a' : g

  -- step (1), case n ≥ m
  definition eq_ge {n m : ℕ} (a : A n) (b : A m) (H : n ≥ m) : i a = i b :=
  calc
    i a = i (fr b H) : eq_same
    ... = i b        : i_fr

  -- step (1), case n ≤ m
  definition eq_le {n m : ℕ} (a : A n) (b : A m) (H : n ≤ m) : i a = i b :=
  calc
    i a = i (fr a H) : i_fr
    ... = i b        : eq_same

  -- step (1), combined
  definition eq_constructors {n m : ℕ} (a : A n) (b : A m) : i a = i b :=
  lt_ge_by_cases (λH, eq_le a b (le_of_lt H)) !eq_ge

  -- some other path operations needed for 2-dimensional path operations
  definition fr_step {n m : ℕ} (a : A n) (H : n ≤ m) : fr a (le.step H) = f (fr a H) := idp

  definition fr_irrel {n m : ℕ} (a : A n) (H H' : n ≤ m) : fr a H = fr a H' :=
  ap (fr a) !is_hprop.elim

  -- TODO: the proofs can probably be slightly simplified if H is expressed in terms of H2
  definition fr_f {n m : ℕ} (a : A n) (H : n ≤ m) (H2 : succ n ≤ m) : fr a H = fr (f a) H2 :=
  begin
    induction H with m H IH,
    { exfalso, exact not_succ_le_self H2},
    { refine _ ⬝ ap (fr (f a)) (to_right_inv !le_equiv_succ_le_succ H2),
      --add some unfold-c's in files
      esimp [le_equiv_succ_le_succ,equiv_of_is_hprop, is_equiv_of_is_hprop],
      revert H IH,
      eapply le.rec_on (le_of_succ_le_succ H2),
      { intros, esimp [succ_le_succ], apply concat,
          apply fr_irrel _ _ (le.step !le.refl),
          reflexivity},
      { intros, rewrite [↑fr,↓fr a H,↓succ_le_succ a_1], exact ap (@f _) !IH}},
  end

  /- 2-dimensional path operations -/

  theorem i_fr_step {n m : ℕ} (a : A n) (H : n ≤ m)
    : i_fr a (le.step H) = g (fr a H) ⬝ i_fr a H := idp

  -- make the next two theorems instances of general theorems about lt_ge_by_cases
  theorem eq_constructors_le {n m : ℕ} (a : A n) (b : A m) (H : n ≤ m)
    : eq_constructors a b = eq_le a b H :=
  begin
    unfold [eq_constructors,lt_ge_by_cases],
    induction (lt_or_ge n m) with H2 H2;all_goals esimp,
    { rewrite [is_hprop.elim H (le_of_lt H2)]},
    { let p := le.antisymm H H2, cases p,
      rewrite [is_hprop.elim H (le.refl m), is_hprop.elim H2 (le.refl m)]; exact !idp_con⁻¹},
  end

  theorem eq_constructors_ge {n m : ℕ} (a : A n) (b : A m) (H : n ≥ m)
    : eq_constructors a b = eq_ge a b H :=
  begin
    unfold [eq_constructors,lt_ge_by_cases],
    induction (lt_or_ge n m) with H2 H2;all_goals esimp,
    { exfalso, apply lt.irrefl, exact lt_of_le_of_lt H H2},
    { rewrite [is_hprop.elim H H2]},
  end

  theorem ap_i_ap_f {n : ℕ} {a a' : A n} (p : a = a')
    : ap i (ap !f p) = !g ⬝ ap i p ⬝ !g⁻¹ :=
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

  theorem i_fr_g {n m : ℕ} (b : A n) (H1 : n ≤ m) (H2 : succ n ≤ m)
    : ap i (fr_f b H1 H2) ⬝ i_fr (f b) H2 ⬝ g b = i_fr b H1 :=
  begin
    induction H1 with m H IH, exfalso, exact not_succ_le_self H2,
    cases H2 with x H3, -- x is unused
    { rewrite [is_hprop.elim H !le.refl,↑fr_f,
      ↑le_equiv_succ_le_succ,▸*],
-- some le.rec's are not reduced if previous line is replaced by "↑le_equiv_succ_le_succ,↑i_fr,↑fr,▸*], state,"
      refine (_ ⬝ !idp_con), apply ap (λx, x ⬝ _), apply (ap (ap i)),
      rewrite [is_hprop_elim_self,↑fr_irrel,▸*,is_hprop_elim_self]},
    { rewrite [↑i_fr,↓i_fr b H,↓i_fr (f b) H3,↓fr (f b) H3,↓fr b H, -IH H3,
        -con.assoc,-con.assoc,-con.assoc],
      apply ap (λx, x ⬝ _ ⬝ _), apply con_eq_of_eq_con_inv, rewrite [-ap_i_ap_f],
      apply ap_i_eq_ap_i_same}
  end -- this was the longest time I've every spent on 14 lines of text

  definition eq_same_con {n : ℕ} (a : A n) {a' a'' : A n} (p : a' = a'')
    : eq_same a a' = eq_same a a'' ⬝ (ap i p)⁻¹ :=
  by induction p; reflexivity

  -- step (2), n > m
  theorem eq_gt_f {n m : ℕ} (a : A n) (b : A m) (H1 : n ≥ succ m) (H2 : n ≥ m)
    : eq_ge a (f b) H1 ⬝ g b = eq_ge a b H2 :=
  begin
    esimp [eq_ge],
    let lem := eq_inv_con_of_con_eq (!con.assoc⁻¹ ⬝ i_fr_g b H2 H1),
    rewrite [con.assoc,lem,-con.assoc], apply ap (λx, x ⬝ _),
    exact !eq_same_con⁻¹
  end

  -- step (2), n ≤ m
  theorem eq_le_f {n m : ℕ} (a : A n) (b : A m) (H1 : n ≤ succ m) (H2 : n ≤ m)
    : eq_le a (f b) H1 ⬝ g b  = eq_le a b H2 :=
  begin
    rewrite [↑eq_le,is_hprop.elim H1 (le.step H2),i_fr_step,con_inv,con.assoc,con.assoc],
    clear H1,
    apply ap (λx, _ ⬝ x),
    rewrite [↑fr,↓fr a H2],
    rewrite -con.assoc, exact !eq_same_f
  end

  -- step (2), combined
  theorem eq_constructors_comp_right {n m : ℕ} (a : A n) (b : A m) :
    eq_constructors a (f b) ⬝ g b = eq_constructors a b :=
  begin
    apply @lt_ge_by_cases m n,
    { intro H, let H2 := le.trans !le_succ H,
      rewrite [eq_constructors_ge a (f b) H,eq_constructors_ge a b H2,eq_gt_f a b H H2]},
    { intro H2, let H := le.trans H2 !le_succ,
      rewrite [eq_constructors_le a (f b) H,eq_constructors_le a b H2,eq_le_f a b H H2]}
  end

  -- induction on b
  definition my_f_eq1 [reducible] (b : my_tr) {n : ℕ} (a : A n) : i a = b :=
  begin
    induction b with m b,
    { apply eq_constructors},
    { apply (equiv.to_inv !pathover_eq_equiv_r), apply eq_constructors_comp_right},
  end

  -- induction on a
  theorem my_f_eq2 (a : my_tr) : Πb, a = b :=
  begin
    induction a,
    { intro b, apply my_f_eq1},
    { apply is_hprop.elimo}
  end

  -- final result
  theorem is_hprop_my_tr : is_hprop my_tr := is_hprop.mk my_f_eq2

end

definition my_trunc.{u} (A : Type.{u}) : Type.{u}                        := @my_tr A
definition tr {A : Type} : A → my_trunc A                                := @i A 0
definition is_hprop_my_trunc (A : Type) : is_hprop (my_trunc A)          := is_hprop_my_tr
definition my_trunc.rec {A : Type} {P : my_trunc A → Type}
  [Pt : Π(x : my_trunc A), is_hprop (P x)]
  (H : Π(a : A), P (tr a)) : Π(x : my_trunc A), P x                      := @rec A P Pt H

example {A : Type} {P : my_trunc A → Type} [Pt : Πaa, is_hprop (P aa)]
        (H : Πa, P (tr a)) (a : A) : (my_trunc.rec H) (tr a) = H a       := by reflexivity
