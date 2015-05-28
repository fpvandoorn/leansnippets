/- NOT FOR BLESSED REPOSITORY -/

import types.eq arity types.pi hit.colimit types.nat.hott types.square

open eq is_trunc unit type_quotient seq_colim is_equiv funext pi nat equiv sum

/- HELPER LEMMAS, which we might want to add to other files -/

  definition inv_con_con_eq_of_eq_con_con_inv {A : Type} {a₁ a₂ b₁ b₂ : A} {p : a₁ = b₁}
    {q : a₁ = a₂} {r : a₂ = b₂} {s : b₁ = b₂} (H : q = p ⬝ s ⬝ r⁻¹) : p⁻¹ ⬝ q ⬝ r = s :=
  begin
    apply con_eq_of_eq_con_inv,
    apply inv_con_eq_of_eq_con,
    rewrite -con.assoc,
    apply H
  end

  theorem is_hprop_elim_self {A : Type} {H : is_hprop A} (x : A) : is_hprop.elim x x = idp :=
  !is_hprop.elim

  definition is_hset_image_of_is_hprop_image {A B : Type} {f : A → B} {a a' : A} (p q : a = a')
    (H : Π(a a' : A), f a = f a') : ap f p = ap f q :=
  have H' : Π{b c : A} (r : b = c), !H⁻¹ ⬝ H a c = ap f r, from
    (λb c r, eq.rec_on r !con.left_inv),
  !H'⁻¹ ⬝ !H'

  inductive le (a : nat) : nat → Type₀ :=
  | base : le a a
  | step : Π {b}, le a b → le a (succ b)

  local infix `≤` := _root_.le
  definition lt [reducible] (n m : ℕ) := succ n ≤ m
  definition ge [reducible] (n m : ℕ) := m ≤ n
  definition gt [reducible] (n m : ℕ) := succ m ≤ n
  local infix `<` := _root_.lt
  local infix `≥` := _root_.ge
  local infix `>` := _root_.gt
  attribute le.base [refl]

abbreviation le.refl (n : ℕ) : n ≤ n := le.base n
definition le_succ (n : ℕ) : n ≤ succ n := le.step !le.base
definition pred_le (n : ℕ) : pred n ≤ n :=
by cases n;all_goals (repeat constructor)
definition le.trans [trans] {n m k : ℕ} (H1 : n ≤ m) (H2 : m ≤ k) : n ≤ k :=
by induction H2 with n H2 IH;exact H1;exact le.step IH
definition le_succ_of_le {n m : ℕ} (H : n ≤ m) : n ≤ succ m := le.trans H !le_succ
definition le_of_succ_le {n m : ℕ} (H : succ n ≤ m) : n ≤ m := le.trans !le_succ H
definition le_of_lt {n m : ℕ} (H : n < m) : n ≤ m := le_of_succ_le H
definition succ_le_succ [unfold-c 3] {n m : ℕ} (H : n ≤ m) : succ n ≤ succ m :=
by induction H;reflexivity;exact le.step v_0
definition pred_le_pred [unfold-c 3] {n m : ℕ} (H : n ≤ m) : pred n ≤ pred m :=
by induction H;reflexivity;cases b;exact v_0;exact le.step v_0
definition le_of_succ_le_succ [unfold-c 3] {n m : ℕ} (H : succ n ≤ succ m) : n ≤ m :=
pred_le_pred H
definition le_succ_of_pred_le [unfold-c 1] {n m : ℕ} (H : pred n ≤ m) : n ≤ succ m :=
by cases n;exact le.step H;exact succ_le_succ H
definition not_succ_le_self {n : ℕ} : ¬succ n ≤ n :=
by induction n with n IH;all_goals intros;cases a;apply IH;exact le_of_succ_le_succ a
definition is_hprop_le [instance] (n m : ℕ) : is_hprop (n ≤ m) :=
begin
  assert lem : Π{n m : ℕ} (p : n ≤ m) (q : n = m), p = q ▸ le.base n,
  { intros, cases p,
    { assert H' : q = idp, apply is_hset.elim,
      cases H', reflexivity},
    { cases q, exfalso, apply not_succ_le_self a}},
  apply is_hprop.mk, intro H1 H2, induction H2,
  { apply lem},
  { cases H1,
    { exfalso, apply not_succ_le_self a},
    { exact ap le.step !v_0}},
end
definition le_equiv_succ_le_succ (n m : ℕ) : (n ≤ m) ≃ (succ n ≤ succ m) :=
equiv_of_is_hprop succ_le_succ le_of_succ_le_succ
definition le_succ_equiv_pred_le (n m : ℕ) : (n ≤ succ m) ≃ (pred n ≤ m) :=
equiv_of_is_hprop pred_le_pred le_succ_of_pred_le
definition zero_le (n : ℕ) : 0 ≤ n :=
by induction n with n IH;apply le.base;exact le.step IH
definition zero_lt_succ (n : ℕ) : 0 < succ n :=
by induction n with n IH;apply le.base;exact le.step IH
definition lt.trans {n m k : ℕ} (H1 : n < m) (H2 : m < k) : n < k :=
le.trans (le.step H1) H2
definition le_lt_trans {n m k : ℕ} (H1 : n ≤ m) (H2 : m < k) : n < k :=
le.trans (succ_le_succ H1) H2
definition lt_le_trans {n m k : ℕ} (H1 : n < m) (H2 : m ≤ k) : n < k :=
le.trans H1 H2
theorem le.antisymm {n m : ℕ} (H1 : n ≤ m) (H2 : m ≤ n) : n = m :=
begin
  cases H1 with m' H1',
  { reflexivity},
  { cases H2 with n' H2',
    { reflexivity},
    { exfalso, apply not_succ_le_self, exact lt.trans H1' H2'}},
end
theorem lt.irrefl (n : ℕ) : ¬n < n := not_succ_le_self
theorem le_lt_antisymm {n m : ℕ} (H1 : n ≤ m) (H2 : m < n) : empty :=
!lt.irrefl (le_lt_trans H1 H2)
theorem lt_le_antisymm {n m : ℕ} (H1 : n < m) (H2 : m ≤ n) : empty :=
le_lt_antisymm H2 H1
theorem lt.antisymm {n m : ℕ} (H1 : n < m) (H2 : m < n) : empty :=
le_lt_antisymm (le_of_lt H1) H2
theorem lt.by_cases {a b : ℕ} {P : Type} (H1 : a < b → P) (H2 : a = b → P) (H3 : b < a → P) : P :=
begin
  revert b H1 H2 H3, induction a with a IH,
  { intros, cases b,
      exact H2 idp,
      exact H1 !zero_lt_succ},
  { intros, cases b with b,
      exact H3 !zero_lt_succ,
    { apply IH,
        intro H, exact H1 (succ_le_succ H),
        intro H, exact H2 (ap succ H),
        intro H, exact H3 (succ_le_succ H)}}
end
theorem lt_or_ge (a b : ℕ) : (a < b) ⊎ (a ≥ b) :=
lt.by_cases inl (λH, inr (eq.rec_on H !le.refl)) (λH, inr (le_of_lt H))
definition lt_ge_by_cases {a b : ℕ} {P : Type} (H1 : a < b → P) (H2 : a ≥ b → P) : P :=
sum.rec_on (lt_or_ge a b) H1 H2

/- definition of "naive truncation" -/

namespace naive_tr
section
  parameters {A : Type}
  variables (a a' : A)

  protected definition R (a a' : A) : Type := unit
  parameter (A)
  definition naive_tr : Type :=
  type_quotient R
  parameter {A}
  definition tr : naive_tr :=
  class_of R a

  definition tr_eq : tr a = tr a' :=
  eq_of_rel _ star

  protected definition rec [recursor] {P : naive_tr → Type} (Pt : Π(a : A), P (tr a))
    (Pe : Π(a a' : A), Pt a =[tr_eq a a'] Pt a') (x : naive_tr) : P x :=
  begin
    fapply (type_quotient.rec_on x),
    { intro a, apply Pt},
    { intro a a' H, cases H, apply Pe}
  end

end
end naive_tr
open naive_tr

section
  parameter {X : Type}

  /- basic constructors -/
  private definition A [reducible] (n : ℕ) : Type := nat.rec_on n X (λn' X', naive_tr X')
  private definition f [reducible] ⦃n : ℕ⦄ (a : A n) : A (succ n)        := tr a
  private definition f_eq [reducible] ⦃n : ℕ⦄ (a a' : A n) : f a = f a'  := tr_eq a a'
  private definition my_tr [reducible] : Type                            := @seq_colim A f
  private definition i [reducible] {n : ℕ} (a : A n) : my_tr             := inclusion f a
  private definition g {n : ℕ} (a : A n)                                 := glue f a

  /-
    The main effort is to prove that my_tr is a mere proposition.
    We do this first by induction on a, and then by induction on b
    On the point level we need to construct
      (1) a : A n, b : A m ⊢ p a b : i a = i b
    On the path level for b we need to show that
      (2) a : A n, b : A m ⊢ p a (f b) ⬝ g b = p a b
    The path level for a is automatic, since (Πb, a = b) is a mere proposition

    For (1) we distinguish the cases n < m and n ≥ m

    For (2) we distinguish the cases n < m, n = m and m > n
  -/

  /- point operations -/

  definition fr [reducible] {n m : ℕ} (a : A n) (H : n ≤ m) : A m :=
  begin
    induction H with m H b,
    { exact a},
    { exact f b},
  end

  /- path operations -/

  definition fr_step {n m : ℕ} (a : A n) (H : n ≤ m) : fr a (le.step H) = f (fr a H) := idp

  definition fr_irrel {n m : ℕ} (a : A n) (H H' : n ≤ m) : fr a H = fr a H' :=
  ap (fr a) !is_hprop.elim

  definition fr_f {n m : ℕ} (a : A n) (H : n ≤ m) (H2 : succ n ≤ m) : fr a H = fr (f a) H2 :=
  begin
    induction H with m H IH,
    { exfalso, exact not_succ_le_self H2},
    { refine _ ⬝ ap (fr (f a)) (to_right_inv !le_equiv_succ_le_succ H2),
      --add some unfold-c's in files
      esimp [le_equiv_succ_le_succ,equiv_of_is_hprop, is_equiv_of_is_hprop],
      revert H IH,
      eapply le.rec_on (le_of_succ_le_succ H2),
      { intros, esimp [succ_le_succ], apply concat, apply ap (fr a),
        exact is_hprop.elim _ (le.step !le.base), reflexivity},
      { intros, rewrite [↑fr,↓fr a H,↓succ_le_succ a_1], exact ap (@f _) !IH}},
  end

  definition i_fr {n m : ℕ} (a : A n) (H : n ≤ m) : i (fr a H) = i a :=
  begin
    induction H with m H IH,
    { reflexivity},
    { exact !g ⬝ IH},
  end

  definition eq_constructors_same {n : ℕ} (a a' : A n) : i a = i a' :=
  calc
    i a = i (f a) : g
        ... = i (f a') : ap i (f_eq a a')
        ... = i a' : g

  -- step (1), case n ≥ m
  definition eq_ge {n m : ℕ} (a : A n) (b : A m) (H : n ≥ m) : i a = i b :=
  calc
    i a = i (fr b H) : eq_constructors_same
    ... = i b        : i_fr

  -- step (1), case n < m
  definition eq_lt {n m : ℕ} (a : A n) (b : A m) (H : n < m) : i a = i b :=
  (eq_ge b a (le_of_lt H))⁻¹

  -- step (1), combined
  definition eq_constructors {n m : ℕ} (a : A n) (b : A m) : i a = i b :=
  lt_ge_by_cases !eq_lt !eq_ge

  /- 2-dimensional path operations -/

  theorem ap_i_ap_f {n : ℕ} {a a' : A n} (p : a = a')
    : ap i (ap !f p) = !g ⬝ ap i p ⬝ !g⁻¹ :=
  eq.rec_on p !con.right_inv⁻¹

  theorem i_fr_step {n m : ℕ} (a : A n) (H : n ≤ m)
    : i_fr a (le.step H) = g (fr a H) ⬝ i_fr a H := idp

  theorem ap_i_eq_ap_i_same {n : ℕ} {a a' : A n} (p q : a = a') : ap i p = ap i q :=
  !is_hset_image_of_is_hprop_image eq_constructors_same

  theorem ap_f_eq_f' {n : ℕ} (a a' : A n)
    : ap i (f_eq (f a) (f a')) = g (f a) ⬝ ap i (f_eq a a') ⬝ (g (f a'))⁻¹ :=
  !ap_i_eq_ap_i_same ⬝ !ap_i_ap_f

  theorem ap_f_eq_f {n : ℕ} (a a' : A n)
    : (g (f a))⁻¹ ⬝ ap i (f_eq (f a) (f a')) ⬝ g (f a') = ap i (f_eq a a') :=
  inv_con_con_eq_of_eq_con_con_inv !ap_f_eq_f'

  theorem eq_constructors_same_f {n : ℕ} (a a' : A n)
    : (g a)⁻¹ ⬝ eq_constructors_same (f a) (f a') ⬝ g a' = eq_constructors_same a a' :=
  begin
   esimp [eq_constructors_same],
   apply (ap (λx, _ ⬝ x ⬝ _)),
   apply (ap_f_eq_f a a'),
  end

  theorem ap_f_eq_inv {n : ℕ} (a a' : A n) : (ap i (f_eq a a'))⁻¹ = (ap i (f_eq a' a)) :=
  by rewrite -ap_inv; apply ap_i_eq_ap_i_same

  theorem eq_constructors_same_inv {n : ℕ} (a a' : A n)
    : (eq_constructors_same a a')⁻¹ = eq_constructors_same a' a :=
  by rewrite [↑eq_constructors_same,+con_inv,inv_inv,ap_f_eq_inv,con.assoc]

  theorem i_fr_g {n m : ℕ} (b : A n) (H1 : n ≤ m) (H2 : succ n ≤ m)
    : ap i (fr_f b H1 H2) ⬝ i_fr (f b) H2 ⬝ g b = i_fr b H1 :=
  begin
    induction H1 with m H IH, exfalso, exact not_succ_le_self H2,
    cases H2 with x H3, -- x is unused
    { rewrite [is_hprop.elim H !le.refl,↑fr_f,
      ↑le_equiv_succ_le_succ,↑i_fr,↑fr,▸*], -- some le.rec's are not reduced
      refine (_ ⬝ !idp_con), apply ap (λx, x ⬝ _), apply (ap (ap i)),
      rewrite [↑le.refl,is_hprop_elim_self,▸*,idp_con,is_hprop_elim_self]},
    { rewrite [↑i_fr,↓i_fr b H,↓i_fr (f b) H3,↓fr (f b) H3,↓fr b H, -IH H3,
        -con.assoc,-con.assoc,-con.assoc],
      apply ap (λx, x ⬝ _ ⬝ _), apply con_eq_of_eq_con_inv, rewrite [-ap_i_ap_f],
      apply ap_i_eq_ap_i_same}
  end -- this was the longest time I've every spent on 14 lines of text

  definition eq_constructors_same_con {n : ℕ} (a : A n) {a' a'' : A n} (p : a' = a'')
    : eq_constructors_same a a' = eq_constructors_same a a'' ⬝ (ap i p)⁻¹ :=
  by induction p; reflexivity

  -- step (2), n > m
  theorem eq_gt_f {n m : ℕ} (a : A n) (b : A m) (H1 : n ≥ succ m) (H2 : n ≥ m)
    : eq_ge a (f b) H1 ⬝ g b = eq_ge a b H2 :=
  begin
    esimp [eq_ge],
    let lem := eq_inv_con_of_con_eq (!con.assoc⁻¹ ⬝ i_fr_g b H2 H1),
    rewrite [con.assoc,lem,-con.assoc], apply ap (λx, x ⬝ _),
    exact !eq_constructors_same_con⁻¹
  end

  theorem eq_eq_f' {n : ℕ} (a b : A n)
    : eq_lt a (f b) (le.base (succ n)) ⬝ g b = eq_ge a b (le.base n) :=
  begin
    esimp [eq_lt,eq_ge,le_of_lt,le_of_succ_le,le.trans,le_succ,i_fr,fr],
    rewrite [con_inv], rewrite [-eq_constructors_same_f a b,eq_constructors_same_inv]
  end

  -- step (2), n = m
  theorem eq_eq_f {n : ℕ} (a b : A n) (H1 : n < succ n) (H2 : n ≤ n)
    : eq_lt a (f b) H1 ⬝ g b = eq_ge a b H2 :=
  by rewrite [is_hprop.elim H1 !le.base, is_hprop.elim H2 !le.base, eq_eq_f']

  theorem eq_lt_f' {n m : ℕ} (a : A n) (b : A m) (H1 : n ≤ succ m) (H2 : n ≤ m)
    : g b ⬝ eq_ge b a H2 = eq_ge (f b) a H1 :=
  begin
    esimp [eq_ge], rewrite [is_hprop.elim H1 (le.step H2),i_fr_step,-con.assoc,-con.assoc], clear H1,
    apply ap (λx, x ⬝ _),
    rewrite [↑fr,↓fr a H2], apply con_eq_of_eq_inv_con,
    rewrite -con.assoc, exact !eq_constructors_same_f⁻¹
  end

  -- step (2), n < m
  theorem eq_lt_f {n m : ℕ} (a : A n) (b : A m) (H1 : n < succ m) (H2 : n < m)
    : eq_lt a (f b) H1 ⬝ g b  = eq_lt a b H2 :=
  by apply inv_con_eq_of_eq_con; apply eq_con_inv_of_con_eq; apply eq_lt_f'

  -- step (2), combined
  theorem eq_constructors_comp_right {n m : ℕ} (a : A n) (b : A m) :
    eq_constructors a (f b) ⬝ g b = eq_constructors a b :=
  begin
    unfold [eq_constructors,lt_ge_by_cases],
    focus (eapply sum.rec_on (lt_or_ge n (succ m));
      all_goals eapply sum.rec_on (lt_or_ge n m);
      all_goals (intro H1 H2;esimp)),
    { apply eq_lt_f},
    { assert H : n = m,
        apply le.antisymm, exact le_of_succ_le_succ H2, exact H1,
      cases H, apply eq_eq_f},
    { exfalso, apply lt.irrefl m, apply lt.trans, exact H2, exact H1},
    { apply eq_gt_f},
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

  -- defining the recursor is easy
  private definition rec {P : my_tr → Type} [Pt : Πx, is_hprop (P x)]
    (H : Π(a : X), P (@i 0 a)) (x : my_tr) : P x :=
  begin
    induction x,
    { induction n with n IH,
      { exact H a},
      { induction a,
        { exact !g⁻¹ ▸ IH a},
        { apply is_hprop.elimo}}},
    { apply is_hprop.elimo}
  end

end

definition my_trunc.{u} (A : Type.{u}) : Type.{u}                        := @my_tr A
definition tr {A : Type} : A → my_trunc A                                := @i A 0
definition is_hprop_my_trunc (A : Type) : is_hprop (my_trunc A)          := is_hprop_my_tr
definition my_trunc.rec {A : Type} {P : my_trunc A → Type}
  [Pt : Π(x : my_trunc A), is_hprop (P x)]
  (H : Π(a : A), P (tr a)) : Π(x : my_trunc A), P x                      := @rec A P Pt H
example {A : Type} {P : my_trunc A → Type} [Pt : Πaa, is_hprop (P aa)]
        (H : Πa, P (tr a)) (a : A) : (my_trunc.rec H) (tr a) = H a       := by reflexivity
