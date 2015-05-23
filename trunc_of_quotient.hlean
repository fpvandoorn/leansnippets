/- NOT FOR BLESSED REPOSITORY -/

import types.eq arity types.pi hit.colimit

open eq is_trunc nat unit type_quotient seq_colim is_equiv funext pi

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

   protected definition rec {P : naive_tr → Type} (Pt : Π(a : A), P (tr a))
    (Pe : Π(a a' : A), Pt a =[tr_eq a a'] Pt a') (x : naive_tr) : P x :=
  begin
    fapply (type_quotient.rec_on x),
    { intro a, apply Pt},
    { intro a a' H, cases H, apply Pe}
  end

  protected definition rec_on [reducible] {P : naive_tr → Type} (x : naive_tr)
    (Pt : Π(a : A), P (tr a))
    (Pe : Π(a a' : A), Pt a =[tr_eq a a'] Pt a') : P x :=
  rec Pt Pe x

  theorem rec_tr_eq {P : naive_tr → Type} (Pt : Π(a : A), P (tr a))
    (Pe : Π(a a' : A), Pt a =[tr_eq a a'] Pt a') (a a' : A)
      : apdo (rec Pt Pe) (tr_eq a a') = Pe a a' :=
  !rec_eq_of_rel

  protected definition elim {P : Type} (Pt : A → P) (Pe : Πa a', Pt a = Pt a') (x : naive_tr) : P :=
  rec Pt (λa a', pathover_of_eq (Pe a a')) x

  protected definition elim_on [reducible] {P : Type} (x : naive_tr)
  (Pt : A → P) (Pe : Πa a', Pt a = Pt a') : P :=
  elim Pt Pe x

  -- theorem elim_tr_eq {P : Type}
  --   (Pincl : Π⦃i : I⦄ (x : A i), P)
  --   (Pglue : Π(j : J) (x : A (dom j)), Pincl (f j x) = Pincl x)
  --     {j : J} (x : A (dom j)) : ap (elim Pincl Pglue) (cglue j x) = Pglue j x :=
  -- begin
  --   apply eq_of_fn_eq_fn_inv !(pathover_constant (cglue j x)),
  --   rewrite [▸*,-apdo_eq_pathover_of_eq_ap,↑elim,rec_cglue],
  -- end

  -- protected definition elim_type (Pincl : Π⦃i : I⦄ (x : A i), Type)
  --   (Pglue : Π(j : J) (x : A (dom j)), Pincl (f j x) ≃ Pincl x) (y : colimit) : Type :=
  -- elim Pincl (λj a, ua (Pglue j a)) y

  -- protected definition elim_type_on [reducible] (y : colimit)
  --   (Pincl : Π⦃i : I⦄ (x : A i), Type)
  --   (Pglue : Π(j : J) (x : A (dom j)), Pincl (f j x) ≃ Pincl x) : Type :=
  -- elim_type Pincl Pglue y

  -- theorem elim_type_cglue (Pincl : Π⦃i : I⦄ (x : A i), Type)
  --   (Pglue : Π(j : J) (x : A (dom j)), Pincl (f j x) ≃ Pincl x)
  --     {j : J} (x : A (dom j)) : transport (elim_type Pincl Pglue) (cglue j x) = Pglue j x :=
  -- by rewrite [tr_eq_cast_ap_fn,↑elim_type,elim_cglue];apply cast_ua_fn

end
end naive_tr
open naive_tr

definition is_hset_image_of_is_hprop_image {A B : Type} {f : A → B} {a a' : A} (p q : a = a')
  (H : Π(a a' : A), f a = f a') : ap f p = ap f q :=
have H' : Π{b c : A} (r : b = c), !H⁻¹ ⬝ H a c = ap f r, from
  (λb c r, eq.rec_on r !con.left_inv),
!H'⁻¹ ⬝ !H'

definition ap_tr_eq_ap_tr {A : Type} {a a' : A} (p q : a = a') : ap tr p = ap tr q :=
!is_hset_image_of_is_hprop_image tr_eq

definition tr_tr_eq_tr_tr {A B : Type} {P : A → B → Type} {a a' : A} {b b' : B}
  (p : a = a') (q : b = b') (x : P a b) : p ▸ q ▸ x = q ▸ p ▸ x :=
eq.rec_on p (eq.rec_on q idp)

abbreviation inc := @inclusion

-- definition transport_colim_rec {A : ℕ → Type} {f : Π⦃n⦄, A n → A (succ n)}
--   {P : seq_colim f → seq_colim f → Type} {aa aa' bb : seq_colim f} (p : aa = aa')
--   (H1 : Π⦃m : ℕ⦄ (b : A m), P aa (inc f b))
--   (H2 : Π⦃m : ℕ⦄ (b : A m), H1 (f b) =[glue f b] H1 b)
--   : p ▸ (seq_colim.rec_on f bb H1 H2)
--       = seq_colim.rec_on f bb (λm b, p ▸ H1 b) (λm b, !tr_tr_eq_tr_tr ⬝ ap (transport _ p) !H2) :=
-- begin
--   apply (eq.rec_on p), esimp
-- end

definition eq_of_homotopy_tr {A : Type} {B : A → Type} {C : Πa, B a → Type}
  {f g : Πa, B a} {H : f ∼ g} {a : A} (c : C a (f a)) :
    eq_of_homotopy H ▸ c = H a ▸ c :=
begin
  apply (homotopy.rec_on H),
  intro p, apply (eq.rec_on p),
  rewrite (left_inv apd10 (refl f))
end

definition eq_of_homotopy_tr2 {A : Type} {B : A → Type} {C : Πa', B a' → Type}
  {f g : Πa, B a} (H : f ∼ g) (c : Πa, C a (f a)) (a : A) :
   (transport _ (eq_of_homotopy H) c) a = H a ▸ c a  :=
begin
  apply (homotopy.rec_on H),
  intro p, apply (eq.rec_on p),
  rewrite (left_inv apd10 (refl f))
end

--set_option pp.notation false
-- definition seq_colim_rec2_on {A : ℕ → Type} {f : Π⦃n⦄, A n → A (succ n)}
--   {P : seq_colim f → seq_colim f → Type} (aa bb : seq_colim f)
--   (Hinc : Π⦃n : ℕ⦄ (a : A n) ⦃m : ℕ⦄ (b : A m), P (inc f a) (inc f b))
--   (Heq1 : Π⦃n : ℕ⦄ (a : A n) ⦃m : ℕ⦄ (b : A m), glue f a ▸ Hinc (f a) b = Hinc a b)
--   (Heq2 : Π⦃n : ℕ⦄ (a : A n) ⦃m : ℕ⦄ (b : A m), glue f b ▸ Hinc a (f b) = Hinc a b)
--     : P aa bb :=
-- begin
--   fapply (seq_colim_rec_on aa),
--     {intros [n, a], fapply (seq_colim_rec_on bb),
--       {exact (Hinc a)},
--       {exact (Heq2 a)}},
--     {intros [n, a], apply concat, apply transport_colim_rec,
--       fapply (apD011 (seq_colim_rec_on bb)),
--         {apply eq_of_homotopy; intro m, apply eq_of_homotopy; intro b, apply Heq1},
--         {apply eq_of_homotopy; intro m, apply eq_of_homotopy; intro b, apply sorry
-- --           rewrite (eq_of_homotopy_tr2 (λm, eq_of_homotopy (λb, Heq1 a b))
-- -- (tr_tr_eq_tr_tr (glue f b) (glue f a) (Hinc (f a) (f b)) ⬝ ap
-- --        (transport (λ (a_2 : seq_colim f), P a_2 (inc f b)) (glue f a))
-- --        (Heq2 (f a) b))
-- -- m)
-- }
-- }
-- end

/- HELPER LEMMAS, which we might want to add to other files -/

  definition add_zero [reducible] (n : ℕ) : 0 + n = n :=
  nat.rec_on n idp (λn p, ap succ p)

  definition add_succ [reducible] (n k : ℕ) : succ n + k = succ (n + k) :=
  nat.rec_on k idp (λn p, ap succ p)

  definition add_comm [reducible] (n k : ℕ) : n + k = k + n :=
  --nat.rec_on k !add_zero (λn p, ap succ p ⬝ !add_succ)
  nat.rec_on n !add_zero (λn p, add_succ n k ⬝ ap succ p)

  definition ap_transport {A : Type} {B : A → Type} {f g : A → A} (p : f ∼ g) {i : A → A}
    (h : Πa, B a → B (i a)) (a : A) (b : B (f a)) : ap i (p a) ▸ h (f a) b = h (g a) (p a ▸ b) :=
  homotopy.rec_on p (λq, eq.rec_on q idp)

  definition ap_pathover {A : Type} {B : A → Type} {f g : A → A} (p : f ∼ g) {i : A → A}
    (h : Πa, B a → B (i a)) (a : A) (b : B (f a)) (b' : B (g a))
    (r : pathover B b (p a) b') : pathover B (h (f a) b) (ap i (p a)) (h (g a) b') :=
  by induction p; induction r using idp_rec_on; exact idpo

  definition inv_con_con_eq_of_eq_con_con_inv {A : Type} {a₁ a₂ b₁ b₂ : A} {p : a₁ = b₁}
    {q : a₁ = a₂} {r : a₂ = b₂} {s : b₁ = b₂} (H : q = p ⬝ s ⬝ r⁻¹) : p⁻¹ ⬝ q ⬝ r = s :=
  begin
    apply con_eq_of_eq_con_inv,
    apply inv_con_eq_of_eq_con,
    rewrite -con.assoc,
    apply H
  end

  definition eq_con_con_inv_of_inv_con_con_eq {A : Type} {a₁ a₂ b₁ b₂ : A} {p : a₁ = b₁}
    {q : a₁ = a₂} {r : a₂ = b₂} {s : b₁ = b₂} (H : p⁻¹ ⬝ q ⬝ r = s) : q = p ⬝ s ⬝ r⁻¹ :=
  begin
    apply eq_con_inv_of_con_eq,
    apply eq_con_of_inv_con_eq,
    rewrite -con.assoc,
    apply H
  end

section
  parameter {X : Type}

  private definition A [reducible] (n : ℕ) : Type :=
  nat.rec_on n X (λn' X', naive_tr X')

  private definition f [reducible] ⦃n : ℕ⦄ (a : A n) : A (succ n) :=
  tr a

  private definition i [reducible] := @inc _ f

  definition my_tr [reducible] := @seq_colim A f

  theorem glue_ap {n : ℕ} {a a' : A n} (p : a = a')
    : ap i (ap !f p) = !glue ⬝ ap i p ⬝ !glue⁻¹ :=
  eq.rec_on p !con.right_inv⁻¹

  definition fr [reducible] {n : ℕ} (k : ℕ) (a : A n) : A (n+k) :=
  nat.rec_on k a (λk' a', f a')

  definition fr_succ {n : ℕ} (k : ℕ) (a : A n) : fr (succ k) a = f (fr k a) := idp

  definition f_fr [reducible] {n : ℕ} (k : ℕ) (a : A n)
    : fr k (f a) =[add_succ n k] f (fr k a) :=
  begin
    induction k with k IH,
    { apply idpo},
    { apply ap_pathover, apply IH}
  end

  -- definition fr_f [reducible] {n : ℕ} (k : ℕ) (a : A n)
  --   : fr k (f a) = (add_succ n k)⁻¹ ▸ f (fr k a) :=
  -- eq_inv_tr_of_tr_eq !f_fr

  definition i_fr [reducible] {n : ℕ} (k : ℕ) (a : A n) : i (fr k a) = i a :=
  nat.rec_on k idp (λk' p', glue f (fr k' a) ⬝ p')

  theorem i_fr_succ {n : ℕ} (k : ℕ) (a : A n) : i_fr (succ k) a = glue f (fr k a) ⬝ i_fr k a :=  idp

  definition eq_constructors_same [reducible] {n : ℕ} (a a' : A n) : i a = i a' :=
  calc
    i a = i (f a) : glue
        ... = i (f a') : ap i (tr_eq a a')
        ... = i a' : glue

  definition eq_constructors_same_eq {n m : ℕ} (a : A n) (a' : A m) (p : n = m) : i a = i a' :=
  by cases p;apply eq_constructors_same

  definition eq_constructors [reducible] {n m : ℕ} (a : A n) (b : A m) : i a = i b :=
  calc
    i a = i (fr m a)                    : i_fr
--    ... = i (f (add_comm m n ▸ fr n b)) : ap i (tr_eq (fr m a) _)
    ... = i (add_comm m n ▸ fr n b)     : eq_constructors_same
    ... = i (fr n b)                    : (apo011 @i (add_comm m n) !pathover_tr)⁻¹
    ... = i b                           : i_fr

  -- print definition eq_constructors --THIS GIVES:
  -- λ (X : Type) (n m : ℕ) (a : A n) (b : A m),
  -- (i_fr m a) ⁻¹ ⬝
  -- eq_constructors_same (fr m a) (add_comm m n ▸ fr n b) ⬝
  -- (apD011 i (add_comm m n) idp) ⁻¹ ⬝
  -- i_fr n b

  --eq_constructors a (f b) ≡
  -- (i_fr (succ m) a) ⁻¹ ⬝
  -- eq_constructors_same (fr (succ m) a) (add_comm (succ m) n ▸ fr n (f b)) ⬝
  -- (apD011 i (add_comm (succ m) n) idp) ⁻¹ ⬝
  -- i_fr n (f b)

  definition eq_constructors_same_con [reducible] {n : ℕ} (a : A n)
    {a' a'' : A n} (p : a' = a'') : eq_constructors_same a a' = eq_constructors_same a a'' ⬝ ap i p⁻¹ :=
  by induction p; reflexivity

  -- set_option pp.implicit true
  -- set_option pp.notation false

  theorem i_fr_glue {m : ℕ} (n : ℕ) (b : A m)
    : i_fr n (f b) ⬝ glue f b
    = apo011 @i (add_succ m n) (f_fr n b) ⬝ glue f (fr n b) ⬝ i_fr n b :=
  begin
    induction n with n IH,
    { reflexivity},
    { rewrite [i_fr_succ,con.assoc, ↓succ m + n, IH, con.assoc,↓i_fr (succ n) b, -con.assoc], clear IH, apply ap (λx, x ⬝ _), apply sorry
--       induction n,
--       { rewrite [↑[fr,add_succ],-idp_con], apply ap (λx, x ⬝ _),
--         induction m, esimp [A] at b, esimp [f_fr]

-- },
--       { }
}
  end

variables
(m : ℕ)
(b : A 0)

-- eval apo011 @i idp (f_fr 1 b)


  theorem eq2_partial {n : ℕ} {a a' : A n} (p q : a = a') : ap i p = ap i q :=
  !is_hset_image_of_is_hprop_image eq_constructors_same

  theorem ap_tr_eq_f' {n : ℕ} (a a' : A n) : ap i (tr_eq (f a) (f a')) =
   (glue f (f a)) ⬝ ap i (tr_eq a a') ⬝ (glue f (f a'))⁻¹ :=
  !eq2_partial ⬝ !glue_ap

  theorem ap_tr_eq_f {n : ℕ} (a a' : A n)
    : (glue f (f a))⁻¹ ⬝ ap i (tr_eq (f a) (f a')) ⬝ (glue f (f a')) =
    ap i (tr_eq a a') :=
  inv_con_con_eq_of_eq_con_con_inv !ap_tr_eq_f'

  theorem eq_constructors_same_f' {n : ℕ} (a a' : A n)
    : !glue⁻¹ ⬝ eq_constructors_same (f a) (f a') ⬝ !glue = eq_constructors_same a a' :=
  begin
   esimp [eq_constructors_same],
   apply (ap (λx, _ ⬝ x ⬝ _)),
   apply (ap_tr_eq_f a a'),
  end

  theorem eq_constructors_same_f {n : ℕ} (a a' : A n) :
    (glue f a)⁻¹ ⬝ eq_constructors_same (f a) (f a') =
    eq_constructors_same a a' ⬝ (glue f a')⁻¹ :=
  eq_con_inv_of_con_eq !eq_constructors_same_f'

  theorem eq_constructors_same_eq_f {n m : ℕ} (a : A n) (a' : A m) (p : n = m) :
    (glue f a)⁻¹ ⬝ eq_constructors_same_eq (f a) (f a') (ap succ p) =
    eq_constructors_same_eq a a' p ⬝ (glue f a')⁻¹ :=
  by cases p; apply eq_constructors_same_f

  definition tr_f {n m : ℕ} (a : A n) (p : n = m) : p ▸ f a = f (p ▸ a) :=
  eq.rec_on p idp

  definition lemma1 {m : ℕ} (n : ℕ) (b : A m)
    : add_comm (succ m) n ▸ fr n (f b) = f (add_comm m n ▸ fr n b) :=
  begin
--    rewrite (fr_f n b),
    apply concat, apply (ap (transport _ _)), apply eq_tr_of_pathover !f_fr,
    -- rewrite -(con_tr (add_succ m n)⁻¹ (add_comm (succ m) n) (f (fr n b)))
    apply concat, apply inverse, apply con_tr,
    -- esimp {add_comm}, --doesn't work
    apply concat, apply (ap (λy, transport A y (f _))),
    apply (inv_con_cancel_left (add_succ m n) (ap succ (add_comm m n))),
    apply ap_transport,
  end

  definition apo011_inv_con {A Z : Type} {B : A → Type} (f : Πa, B a → Z) {a a' a'' : A}
    {b : B a} {b' : B a'} {b'' : B a''} (Ha : a' = a) (Ha' : a' = a'')
    (Hb : b' =[Ha] b) (Hb' : b' =[Ha'] b'')
      : (apo011 f Ha Hb)⁻¹ ⬝ apo011 f Ha' Hb' = apo011 f (Ha⁻¹ ⬝ Ha') (Hb⁻¹ᵒ ⬝o Hb') :=
  by cases Hb; cases Hb'; reflexivity

--eq_constructors_same (fr m a) (add_comm (succ m) n ▸ fr n b)
-- ⬝ (glue f (add_comm (succ m) n ▸ fr n b))⁻¹ᵖ
  --sorry

  -- set_option pp.notation false
  -- set_option pp.implicit true
  -- set_option pp.universes true
  -- set_option pp.full_names true
  -- set_option pp.abbreviations false
  -- set_option pp.coercions true
  -- set_option pp.beta false
--  set_option pp.metavar_args true

  theorem eq_constructors_comp_right {n m : ℕ} (a : A n) (b : A m) :
    eq_constructors a (f b) ⬝ glue f b = eq_constructors a b :=
  begin
    unfold eq_constructors, rewrite [con.assoc _ !i_fr !glue, i_fr_glue,
      -con.assoc _ _ !i_fr, -con.assoc _ _ !glue,con.assoc _ _⁻¹ _, apo011_inv_con,
      i_fr_succ,con_inv,con.assoc _⁻¹ _⁻¹ _],
    apply ap (λx, x ⬝ _),
    apply concat, apply ap (λx, _ ⬝ x ⬝ _ ⬝ _),
    apply concat, apply ap (λx, _ ⬝ x), apply eq_constructors_same_con, apply lemma1,
    rewrite -con.assoc, apply ap (λx, x ⬝ _), apply eq_constructors_same_f,
    rewrite +con.assoc,
    apply ap (λx, _ ⬝ (_ ⬝ (_ ⬝ (_ ⬝ x)))),
    --unfold lemma1,
  end
  check @lemma1
  check @fr_succ
  print lemma1

  definition my_tr_eq1 [reducible] (b : my_tr) {n : ℕ} (a : A n) : i a = b :=
  begin
    induction b with m b,
    { apply eq_constructors},
    { apply (equiv.to_inv !pathover_eq_equiv_r), apply eq_constructors_comp_right},
  end

  theorem my_tr_eq2 (a : my_tr) : Πb, a = b :=
  begin
    induction a,
    { intro b, apply my_tr_eq1},
    { apply is_hprop.elimo}
  end

  theorem is_hprop_my_tr : is_hprop my_tr :=
  is_hprop.mk my_tr_eq2

end


  -- private definition fcomm_eq [reducible] {n : ℕ} (a : A n) : i (fcomm a) = i a :=
  -- sorry

  -- definition eq_constructors_same_eq'' {n : ℕ} (a a' : A n) : ap i (tr_eq (f a) (f a')) =
  --  (glue f (f a)) ⬝ ap i (tr_eq a a') ⬝ (glue f (f a'))⁻¹ :=
  -- !eq2_partial ⬝ !glue2

  -- definition eq_constructors_same_eq' {n : ℕ} (a a' : A n)
  --   : (glue f (f a))⁻¹ ⬝ ap i (tr_eq (f a) (f a')) ⬝ (glue f (f a')) =
  --   ap i (tr_eq a a') :=
  -- inv_con_con_eq_of_eq_con_con_inv !eq_constructors_same_eq''

  -- theorem eq_constructors_same_eq2 {n : ℕ} (a a' : A n)
  --   : !glue⁻¹ ⬝ eq_constructors_same (f a) (f a') ⬝ !glue = eq_constructors_same a a' :=
  -- begin
  --  esimp {eq_constructors_same},
  --  apply (ap (λx, _ ⬝ x ⬝ _)),
  --  apply (eq_constructors_same_eq' a a'),
  -- end

  -- theorem eq_constructors_same_eq {n : ℕ} (a a' : A n)
  --   : eq_constructors_same (f a) (f a') = !glue ⬝ eq_constructors_same a a' ⬝ !glue⁻¹ :=
  -- eq_con_con_inv_of_inv_con_con_eq !eq_constructors_same_eq2

  -- definition eq_constructors_same2 [reducible] {n k : ℕ} (b : A (n + k)) (a : A n) : i b = i a :=
  -- !eq_constructors_same ⬝ !i_fr

  -- definition eq_constructors_same2_eq {n k : ℕ} (b : A (n + k)) (a : A n) : @eq_constructors_same2 n (succ k) (f b) a =
  --   glue f b ⬝ eq_constructors_same2 b a :=
  -- sorry

  -- definition eq_constructors_same3 [reducible] {n k : ℕ} (b : A (k + n)) (a : A n) : i b = i a :=
  -- apd011 @i !add_comm idp ⬝ eq_constructors_same2 (!add_comm ▸ b) a

  -- definition eq_constructors [reducible] {n m : ℕ} (a : A n) (b : A m) : i a = i b :=
  -- calc
  --   i a = i (fr m a) : i_fr
  --       ... = i b        : eq_constructors_same3
