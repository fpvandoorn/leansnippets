/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn
-/

import homotopy.circle eq2 algebra.e_closure cubical.squareover cubical.cube

open quotient eq circle sum sigma equiv function relation

  /-
    This files defines a general class of nonrecursive HITs using just quotients.
    We can define any HIT X which has
    - a single 0-constructor
       f : A → X (for some type A)
    - a single 1-constructor
       e : Π{a a' : A}, R a a' → a = a' (for some (type-valued) relation R on A)
    and furthermore has 2-constructors which are all of the form
    p = p'
    where p, p' are of the form
    - refl (f a), for some a : A;
    - e r, for some r : R a a';
    - ap f q, where q : a = a';
    - inverses of such paths;
    - concatenations of such paths.

    so an example 2-constructor could be (as long as it typechecks):
      ap f q' ⬝ ((e r)⁻¹ ⬝ ap f q)⁻¹ ⬝ e r' = idp
  -/


section
  variables {A A' : Type} {B : A → Type}
            {a a' a'' a₀₀ a₂₀ a₄₀ a₀₂ a₂₂ a₂₄ a₀₄ a₄₂ a₄₄ : A}
            /-a₀₀-/ {p₁₀ : a₀₀ = a₂₀} /-a₂₀-/ {p₃₀ : a₂₀ = a₄₀} /-a₄₀-/
       {p₀₁ : a₀₀ = a₀₂} /-s₁₁-/ {p₂₁ : a₂₀ = a₂₂} /-s₃₁-/ {p₄₁ : a₄₀ = a₄₂}
            /-a₀₂-/ {p₁₂ : a₀₂ = a₂₂} /-a₂₂-/ {p₃₂ : a₂₂ = a₄₂} /-a₄₂-/
       {p₀₃ : a₀₂ = a₀₄} /-s₁₃-/ {p₂₃ : a₂₂ = a₂₄} /-s₃₃-/ {p₄₃ : a₄₂ = a₄₄}
            /-a₀₄-/ {p₁₄ : a₀₄ = a₂₄} /-a₂₄-/ {p₃₄ : a₂₄ = a₄₄} /-a₄₄-/
            {s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁}
            {b₀₀ : B a₀₀} {b₂₀ : B a₂₀} {b₄₀ : B a₄₀}
            {b₀₂ : B a₀₂} {b₂₂ : B a₂₂} {b₄₂ : B a₄₂}
            {b₀₄ : B a₀₄} {b₂₄ : B a₂₄} {b₄₄ : B a₄₄}
            /-b₀₀-/ {q₁₀ : b₀₀ =[p₁₀] b₂₀} /-b₂₀-/ {q₃₀ : b₂₀ =[p₃₀] b₄₀} /-b₄₀-/
   {q₀₁ : b₀₀ =[p₀₁] b₀₂} /-t₁₁-/ {q₂₁ : b₂₀ =[p₂₁] b₂₂} /-t₃₁-/ {q₄₁ : b₄₀ =[p₄₁] b₄₂}
            /-b₀₂-/ {q₁₂ : b₀₂ =[p₁₂] b₂₂} /-b₂₂-/ {q₃₂ : b₂₂ =[p₃₂] b₄₂} /-b₄₂-/
   {q₀₃ : b₀₂ =[p₀₃] b₀₄} /-t₁₃-/ {q₂₃ : b₂₂ =[p₂₃] b₂₄} /-t₃₃-/ {q₄₃ : b₄₂ =[p₄₃] b₄₄}
            /-b₀₄-/ {q₁₄ : b₀₄ =[p₁₄] b₂₄} /-b₂₄-/ {q₃₄ : b₂₄ =[p₃₄] b₄₄} /-b₄₄-/

  definition apdo_change_path {B : A → Type} {a a₂ : A} (f : Πa, B a) {p p' : a = a₂} (s : p = p')
    : apdo f p' = change_path s (apdo f p) :=
  by induction s; reflexivity

--  set_option pp.notation false
  -- definition pathover_of_hdeg_squareover' {q₂₁ : p₁₀ ▸ b₀₀ =[p₂₁] p₁₂ ▸ b₀₂}
  --   (r : pathover _ q₀₁ _ q₂₁)
  --   : squareover B s₁₁ (pathover_tr p₁₀ b₀₀) (pathover_tr p₁₂ b₀₂) q₀₁ q₂₁ :=
  -- begin

  -- end

end



namespace simple_two_quotient

  section
  parameters {A : Type}
             (R : A → A → Type)
  local abbreviation T := e_closure R -- the (type-valued) equivalence closure of R
  parameter  (Q : Π⦃a⦄, T a a → Type)
  variables ⦃a a' : A⦄ {s : R a a'} {r : T a a}


  local abbreviation B := A ⊎ Σ(a : A) (r : T a a), Q r

  inductive pre_two_quotient_rel : B → B → Type :=
  | pre_Rmk {} : Π⦃a a'⦄ (r : R a a'), pre_two_quotient_rel (inl a) (inl a')
  --BUG: if {} not provided, the alias for pre_Rmk is wrong

  definition pre_two_quotient := quotient pre_two_quotient_rel

  open pre_two_quotient_rel
  local abbreviation C := quotient pre_two_quotient_rel
  protected definition j [constructor] (a : A) : C := class_of pre_two_quotient_rel (inl a)
  protected definition pre_aux [constructor] (q : Q r) : C :=
  class_of pre_two_quotient_rel (inr ⟨a, r, q⟩)
  protected definition e (s : R a a') : j a = j a' := eq_of_rel _ (pre_Rmk s)
  protected definition et (t : T a a') : j a = j a' := e_closure.elim e t
  protected definition f [unfold 7] (q : Q r) : S¹ → C :=
  circle.elim (j a) (et r)

  protected definition pre_rec [unfold 8] {P : C → Type}
    (Pj : Πa, P (j a)) (Pa : Π⦃a : A⦄ ⦃r : T a a⦄ (q : Q r), P (pre_aux q))
    (Pe : Π⦃a a' : A⦄ (s : R a a'), Pj a =[e s] Pj a') (x : C) : P x :=
  begin
    induction x with p,
    { induction p,
      { apply Pj},
      { induction a with a1 a2, induction a2, apply Pa}},
    { induction H, esimp, apply Pe},
  end

  protected definition pre_elim [unfold 8] {P : Type} (Pj : A → P)
    (Pa : Π⦃a : A⦄ ⦃r : T a a⦄, Q r → P) (Pe : Π⦃a a' : A⦄ (s : R a a'), Pj a = Pj a') (x : C)
    : P :=
  pre_rec Pj Pa (λa a' s, pathover_of_eq (Pe s)) x

  protected theorem rec_e {P : C → Type}
    (Pj : Πa, P (j a)) (Pa : Π⦃a : A⦄ ⦃r : T a a⦄ (q : Q r), P (pre_aux q))
    (Pe : Π⦃a a' : A⦄ (s : R a a'), Pj a =[e s] Pj a') ⦃a a' : A⦄ (s : R a a')
    : apdo (pre_rec Pj Pa Pe) (e s) = Pe s :=
  !rec_eq_of_rel

  protected theorem elim_e {P : Type} (Pj : A → P) (Pa : Π⦃a : A⦄ ⦃r : T a a⦄, Q r → P)
    (Pe : Π⦃a a' : A⦄ (s : R a a'), Pj a = Pj a') ⦃a a' : A⦄ (s : R a a')
    : ap (pre_elim Pj Pa Pe) (e s) = Pe s :=
  begin
    apply eq_of_fn_eq_fn_inv !(pathover_constant (e s)),
    rewrite [▸*,-apdo_eq_pathover_of_eq_ap,↑pre_elim,rec_e],
  end

  protected definition elim_et {P : Type} (Pj : A → P) (Pa : Π⦃a : A⦄ ⦃r : T a a⦄, Q r → P)
    (Pe : Π⦃a a' : A⦄ (s : R a a'), Pj a = Pj a') ⦃a a' : A⦄ (t : T a a')
    : ap (pre_elim Pj Pa Pe) (et t) = e_closure.elim Pe t :=
  ap_e_closure_elim_h e (elim_e Pj Pa Pe) t

  protected definition rec_et {P : C → Type}
    (Pj : Πa, P (j a)) (Pa : Π⦃a : A⦄ ⦃r : T a a⦄ (q : Q r), P (pre_aux q))
    (Pe : Π⦃a a' : A⦄ (s : R a a'), Pj a =[e s] Pj a') ⦃a a' : A⦄ (t : T a a')
    : apdo (pre_rec Pj Pa Pe) (et t) = e_closure.elimo e Pe t :=
  ap_e_closure_elimo_h e Pe (rec_e Pj Pa Pe) t

  inductive simple_two_quotient_rel : C → C → Type :=
  | Rmk {} : Π{a : A} {r : T a a} (q : Q r) (x : circle),
      simple_two_quotient_rel (f q x) (pre_aux q)

  open simple_two_quotient_rel
  definition simple_two_quotient := quotient simple_two_quotient_rel
  local abbreviation D := simple_two_quotient
  local abbreviation i := class_of simple_two_quotient_rel
  definition incl0 (a : A) : D := i (j a)
  protected definition aux (q : Q r) : D := i (pre_aux q)
  definition incl1 (s : R a a') : incl0 a = incl0 a' := ap i (e s)
  definition inclt (t : T a a') : incl0 a = incl0 a' := e_closure.elim incl1 t
  -- "wrong" version inclt, which is ap i (p ⬝ q) instead of ap i p ⬝ ap i q
  -- it is used in the proof, because incltw is easier to work with
  protected definition incltw (t : T a a') : incl0 a = incl0 a' := ap i (et t)

  protected definition inclt_eq_incltw (t : T a a') : inclt t = incltw t :=
  (ap_e_closure_elim i e t)⁻¹

  definition incl2' (q : Q r) (x : S¹) : i (f q x) = aux q :=
  eq_of_rel simple_two_quotient_rel (Rmk q x)

  protected definition incl2w (q : Q r) : incltw r = idp :=
  (ap02 i (elim_loop (j a) (et r))⁻¹) ⬝
  (ap_compose i (f q) loop)⁻¹ ⬝
  ap_is_constant (incl2' q) loop ⬝
  !con.right_inv

  definition incl2 (q : Q r) : inclt r = idp :=
  inclt_eq_incltw r ⬝ incl2w q

  local attribute simple_two_quotient f i D incl0 aux incl1 incl2' inclt [reducible]
  local attribute i aux incl0 [constructor]
  protected definition elim {P : Type} (P0 : A → P)
    (P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a')
    (P2 : Π⦃a : A⦄ ⦃r : T a a⦄ (q : Q r), e_closure.elim P1 r = idp)
    (x : D) : P :=
  begin
    induction x,
    { refine (pre_elim _ _ _ a),
      { exact P0},
      { intro a r q, exact P0 a},
      { exact P1}},
    { exact abstract begin induction H, induction x,
      { exact idpath (P0 a)},
      { unfold f, apply eq_pathover, apply hdeg_square,
        exact abstract ap_compose (pre_elim P0 _ P1) (f q) loop ⬝
              ap _ !elim_loop ⬝
              !elim_et ⬝
              P2 q ⬝
              !ap_constant⁻¹ end} end end},
  end
  local attribute elim [unfold 8]

  --check eq_of_hdeg_square
variables
(P : D → Type)
(P0 : Π (a : A), P (incl0 a))
(P1 : Π ⦃a a' : A⦄ (s : R a a'), P0 a =[ incl1 s ] P0 a')
(P2 :
  Π ⦃a : A⦄ ⦃r : T a a⦄ (q : Q r),
    squareover P (vdeg_square (incl2 q)) (e_closure.elimo incl1 P1 r) idpo idpo idpo)
(q : Q r)
(a_1 : S¹)
-- exit
  print pathover_tr
  print pathover_ap
  print pathover_of_pathover_ap
  check (λ(x : incl0 a = aux q), x) (incl2' q base)
  check (natural_square_tr (incl2' q) loop)
  check f q
  print apdo
  print incl1
  protected definition rec {P : D → Type} (P0 : Π(a : A), P (incl0 a))
    (P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a =[incl1 s] P0 a')
    (P2 : Π⦃a : A⦄ ⦃r : T a a⦄ (q : Q r),
      change_path (incl2 q) (e_closure.elimo incl1 P1 r) = idpo)
    (x : D) : P x :=
  begin
    induction x,
    { refine (pre_rec _ _ _ a),
      { exact P0},
      { intro a r q, exact incl2' q base ▸ P0 a},
      { intro a a' s, exact pathover_of_pathover_ap P i (P1 s)}},
    { exact abstract begin induction H, induction x,
      { esimp, exact pathover_tr (incl2' q base) (P0 a)},
      { apply pathover_pathover,
        esimp, fold [i, incl2' q],
        check_expr (natural_square_tr (incl2' q) loop), state,
        refine eq_hconcato _ _, rotate 1,
        { transitivity _,
          { apply ap (pathover_ap _ _),
            transitivity _, apply apdo_compose2 (pre_rec P0 _ _) (f q) loop,
            apply ap (pathover_of_pathover_ap _ _),
            transitivity _, apply apdo_change_path, exact !elim_loop⁻¹,
            apply ap (change_path _),
            apply rec_et},
          fold [i], },
--        fold [incl2 q]
--        apply ap _ !elim_loop,

        -- apply hdeg_square,
        -- exact abstract ap_compose (pre_elim P0 _ P1) (f q) loop ⬝
        --       ap _ !elim_loop ⬝
        --       !elim_et ⬝
        --       P2 q ⬝
        --       !ap_constant⁻¹ end
} end end},
  end
exit
  -- definition elim_unique {P : Type} {f g : D → P}
  --   (p0 : Π(a : A), f (incl0 a) = g (incl0 a))
  --   (p1 : Π⦃a a' : A⦄ (s : R a a'), square (ap f (incl1 s)) (ap g (incl1 s)) (p0 a) (p0 a'))
  --   (p2 : Π⦃a : A⦄ ⦃r : T a a⦄ (q : Q r),
  --     cube (hdeg_square (ap02 f (incl2 q))) (hdeg_square (ap02 g (incl2 q)))
  --          _ _ _ _)
  --   (x : D) : f x = g x :=
  -- sorry






 --  set_option pp.notation false
 --  protected theorem elim_unique {P : Type} (f : D → P) (d : D) :
 --    elim (λa, f (incl0 a))
 --         (λa a' s, ap f (incl1 s))
 --         (λa r q, !ap_e_closure_elim⁻¹ ⬝ ap (ap f) (incl2 q))
 --         d = f d :=
 --  begin
 --    induction d,
 --    { refine (pre_rec _ _ _ a),
 --      { clear a, intro a, reflexivity},
 --      { clear a, intro a r q, rewrite [↑incl0,↓i], exact ap f (incl2' q base)},
 --      { clear a, intro a a' s, esimp,
 --        apply eq_pathover, apply hdeg_square,
 --        rewrite [elim_e,ap_compose f (class_of simple_two_quotient_rel)]}},
 --    { induction H, esimp, apply eq_pathover, induction x,
 --      { esimp, rewrite [↓pre_two_quotient], esimp, rewrite [↓incl2' q base],
 --        /- PREVIOUS REWRITE FAILS -/
 --        xrewrite [elim_incl2'], apply square_of_eq, reflexivity},
 --      { esimp, apply sorry --apply square_pathover,


 -- }}
 --  end
/-
exit
  begin
    { exact abstract begin induction H, induction x,
      { exact idpath (P0 a)},
      { unfold f, apply eq_pathover, apply hdeg_square,
        exact abstract ap_compose (pre_elim P0 _ P1) (f q) loop ⬝
              ap _ !elim_loop ⬝
              !elim_et ⬝
              P2 q ⬝
              !ap_constant⁻¹ end
} end end},
  end
-/


  protected definition elim_on {P : Type} (x : D) (P0 : A → P)
    (P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a')
    (P2 : Π⦃a : A⦄ ⦃r : T a a⦄ (q : Q r), e_closure.elim P1 r = idp)
     : P :=
  elim P0 P1 P2 x

  definition elim_incl1 {P : Type} {P0 : A → P}
    {P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a'}
    (P2 : Π⦃a : A⦄ ⦃r : T a a⦄ (q : Q r), e_closure.elim P1 r = idp)
    ⦃a a' : A⦄ (s : R a a') : ap (elim P0 P1 P2) (incl1 s) = P1 s :=
  (ap_compose (elim P0 P1 P2) i (e s))⁻¹ ⬝ !elim_e

  definition elim_inclt [unfold 10] {P : Type} {P0 : A → P}
    {P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a'}
    (P2 : Π⦃a : A⦄ ⦃r : T a a⦄ (q : Q r), e_closure.elim P1 r = idp)
    ⦃a a' : A⦄ (t : T a a') : ap (elim P0 P1 P2) (inclt t) = e_closure.elim P1 t :=
  ap_e_closure_elim_h incl1 (elim_incl1 P2) t

  protected definition elim_incltw {P : Type} {P0 : A → P}
    {P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a'}
    (P2 : Π⦃a : A⦄ ⦃r : T a a⦄ (q : Q r), e_closure.elim P1 r = idp)
    ⦃a a' : A⦄ (t : T a a') : ap (elim P0 P1 P2) (incltw t) = e_closure.elim P1 t :=
  (ap_compose (elim P0 P1 P2) i (et t))⁻¹ ⬝ !elim_et

  protected theorem elim_inclt_eq_elim_incltw {P : Type} {P0 : A → P}
    {P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a'}
    (P2 : Π⦃a : A⦄ ⦃r : T a a⦄ (q : Q r), e_closure.elim P1 r = idp)
    ⦃a a' : A⦄ (t : T a a')
    : elim_inclt P2 t = ap (ap (elim P0 P1 P2)) (inclt_eq_incltw t) ⬝ elim_incltw P2 t :=
  begin
    unfold [elim_inclt,elim_incltw,inclt_eq_incltw,et],
    refine !ap_e_closure_elim_h_eq ⬝ _,
    rewrite [ap_inv,-con.assoc],
    xrewrite [eq_of_square (ap_ap_e_closure_elim i (elim P0 P1 P2) e t)⁻¹ʰ],
    rewrite [↓incl1,con.assoc], apply whisker_left,
    rewrite [↑[elim_et,elim_incl1],+ap_e_closure_elim_h_eq,con_inv,↑[i,function.compose]],
    rewrite [-con.assoc (_ ⬝ _),con.assoc _⁻¹,con.left_inv,▸*,-ap_inv,-ap_con],
    apply ap (ap _),
    krewrite [-eq_of_homotopy3_inv,-eq_of_homotopy3_con]
  end

  definition elim_incl2' {P : Type} {P0 : A → P}
    {P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a'}
    (P2 : Π⦃a : A⦄ ⦃r : T a a⦄ (q : Q r), e_closure.elim P1 r = idp)
    ⦃a : A⦄ ⦃r : T a a⦄ (q : Q r) : ap (elim P0 P1 P2) (incl2' q base) = idpath (P0 a) :=
  !elim_eq_of_rel

  -- set_option pp.implicit true
  protected theorem elim_incl2w {P : Type} (P0 : A → P)
    (P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a')
    (P2 : Π⦃a : A⦄ ⦃r : T a a⦄ (q : Q r), e_closure.elim P1 r = idp)
    ⦃a : A⦄ ⦃r : T a a⦄ (q : Q r)
    : square (ap02 (elim P0 P1 P2) (incl2w q)) (P2 q) (elim_incltw P2 r) idp :=
  begin
    esimp [incl2w,ap02],
    rewrite [+ap_con (ap _),▸*],
    xrewrite [-ap_compose (ap _) (ap i)],
    rewrite [+ap_inv],
    xrewrite [eq_top_of_square
               ((ap_compose_natural (elim P0 P1 P2) i (elim_loop (j a) (et r)))⁻¹ʰ⁻¹ᵛ ⬝h
               (ap_ap_compose (elim P0 P1 P2) i (f q) loop)⁻¹ʰ⁻¹ᵛ ⬝h
               ap_ap_is_constant (elim P0 P1 P2) (incl2' q) loop ⬝h
               ap_con_right_inv_sq (elim P0 P1 P2) (incl2' q base)),
               ↑[elim_incltw]],
    apply whisker_tl,
    rewrite [ap_is_constant_eq],
    xrewrite [naturality_apdo_eq (λx, !elim_eq_of_rel) loop],
    rewrite [↑elim_2,rec_loop,square_of_pathover_concato_eq,square_of_pathover_eq_concato,
            eq_of_square_vconcat_eq,eq_of_square_eq_vconcat],
    apply eq_vconcat,
    { apply ap (λx, _ ⬝ eq_con_inv_of_con_eq ((_ ⬝ x ⬝ _)⁻¹ ⬝ _) ⬝ _),
      transitivity _, apply ap eq_of_square,
        apply to_right_inv !eq_pathover_equiv_square (hdeg_square (elim_1 P A R Q P0 P1 a r q P2)),
      transitivity _, apply eq_of_square_hdeg_square,
      unfold elim_1, reflexivity},
    rewrite [+con_inv,whisker_left_inv,+inv_inv,-whisker_right_inv,
             con.assoc (whisker_left _ _),con.assoc _ (whisker_right _ _),▸*,
             whisker_right_con_whisker_left _ !ap_constant],
    xrewrite [-con.assoc _ _ (whisker_right _ _)],
    rewrite [con.assoc _ _ (whisker_left _ _),idp_con_whisker_left,▸*,
             con.assoc _ !ap_constant⁻¹,con.left_inv],
    xrewrite [eq_con_inv_of_con_eq_whisker_left,▸*],
    rewrite [+con.assoc _ _ !con.right_inv,
             right_inv_eq_idp (
               (λ(x : ap (elim P0 P1 P2) (incl2' q base) = idpath
               (elim P0 P1 P2 (class_of simple_two_quotient_rel (f q base)))), x)
                (elim_incl2' P2 q)),
             ↑[whisker_left]],
    xrewrite [con2_con_con2],
    rewrite [idp_con,↑elim_incl2',con.left_inv,whisker_right_inv,↑whisker_right],
    xrewrite [con.assoc _ _ (_ ◾ _)],
    rewrite [con.left_inv,▸*,-+con.assoc,con.assoc _⁻¹,↑[elim,function.compose],con.left_inv,
             ▸*,↑j,con.left_inv,idp_con],
    apply square_of_eq, reflexivity
  end

  theorem elim_incl2 {P : Type} (P0 : A → P)
    (P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a')
    (P2 : Π⦃a : A⦄ ⦃r : T a a⦄ (q : Q r), e_closure.elim P1 r = idp)
    ⦃a : A⦄ ⦃r : T a a⦄ (q : Q r)
    : square (ap02 (elim P0 P1 P2) (incl2 q)) (P2 q) (elim_inclt P2 r) idp :=
  begin
    rewrite [↑incl2,↑ap02,ap_con,elim_inclt_eq_elim_incltw],
    apply whisker_tl,
    apply elim_incl2w
  end

end
end simple_two_quotient

--attribute simple_two_quotient.j [constructor] --TODO
attribute /-simple_two_quotient.rec-/ simple_two_quotient.elim [unfold 8] [recursor 8]
--attribute simple_two_quotient.elim_type [unfold 9]
attribute /-simple_two_quotient.rec_on-/ simple_two_quotient.elim_on [unfold 5]
--attribute simple_two_quotient.elim_type_on [unfold 6]

namespace two_quotient
  open e_closure simple_two_quotient
  section
  parameters {A : Type}
             (R : A → A → Type)
  local abbreviation T := e_closure R -- the (type-valued) equivalence closure of R
  parameter  (Q : Π⦃a a'⦄, T a a' → T a a' → Type)
  variables ⦃a a' : A⦄ {s : R a a'} {t t' : T a a'}

  inductive two_quotient_Q : Π⦃a : A⦄, e_closure R a a → Type :=
  | Qmk : Π⦃a a' : A⦄ ⦃t t' : T a a'⦄, Q t t' → two_quotient_Q (t ⬝r t'⁻¹ʳ)
  open two_quotient_Q
  local abbreviation Q2 := two_quotient_Q

  definition two_quotient := simple_two_quotient R Q2
  definition incl0 (a : A) : two_quotient := incl0 _ _ a
  definition incl1 (s : R a a') : incl0 a = incl0 a' := incl1 _ _ s
  definition inclt (t : T a a') : incl0 a = incl0 a' := e_closure.elim incl1 t
  definition incl2 (q : Q t t') : inclt t = inclt t' :=
  eq_of_con_inv_eq_idp (incl2 _ _ (Qmk R q))

  protected definition elim {P : Type} (P0 : A → P)
    (P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a')
    (P2 : Π⦃a a' : A⦄ ⦃t t' : T a a'⦄ (q : Q t t'), e_closure.elim P1 t = e_closure.elim P1 t')
    (x : two_quotient) : P :=
  begin
    induction x,
    { exact P0 a},
    { exact P1 s},
    { exact abstract [unfold 10] begin induction q with a a' t t' q,
      rewrite [↑e_closure.elim],
      apply con_inv_eq_idp, exact P2 q end end},
  end
  local attribute elim [unfold 8]

  protected definition elim_on {P : Type} (x : two_quotient) (P0 : A → P)
    (P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a')
    (P2 : Π⦃a a' : A⦄ ⦃t t' : T a a'⦄ (q : Q t t'), e_closure.elim P1 t = e_closure.elim P1 t')
     : P :=
  elim P0 P1 P2 x

  definition elim_incl1 {P : Type} {P0 : A → P}
    {P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a'}
    (P2 : Π⦃a a' : A⦄ ⦃t t' : T a a'⦄ (q : Q t t'), e_closure.elim P1 t = e_closure.elim P1 t')
    ⦃a a' : A⦄ (s : R a a') : ap (elim P0 P1 P2) (incl1 s) = P1 s :=
  !elim_incl1

  definition elim_inclt {P : Type} {P0 : A → P}
    {P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a'}
    (P2 : Π⦃a a' : A⦄ ⦃t t' : T a a'⦄ (q : Q t t'), e_closure.elim P1 t = e_closure.elim P1 t')
    ⦃a a' : A⦄ (t : T a a') : ap (elim P0 P1 P2) (inclt t) = e_closure.elim P1 t :=
  !elim_inclt --ap_e_closure_elim_h incl1 (elim_incl1 P2) t






--set_option pp.full_names true
print simple_two_quotient.elim_inclt
print eq_of_con_inv_eq_idp
  --print elim
  theorem elim_incl2 {P : Type} (P0 : A → P)
    (P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a')
    (P2 : Π⦃a a' : A⦄ ⦃t t' : T a a'⦄ (q : Q t t'), e_closure.elim P1 t = e_closure.elim P1 t')
    ⦃a a' : A⦄ ⦃t t' : T a a'⦄ (q : Q t t')
    : square (ap02 (elim P0 P1 P2) (incl2 q)) (P2 q) (elim_inclt P2 t) (elim_inclt P2 t') :=
  begin
    rewrite [↑[incl2,elim],ap_eq_of_con_inv_eq_idp],
    xrewrite [eq_top_of_square (elim_incl2 R Q2 P0 P1 (elim_1 A R Q P P0 P1 P2) (Qmk R q))],
--    esimp, --doesn't fold elim_inclt back. The following tactic is just a "custom esimp"
    xrewrite [{simple_two_quotient.elim_inclt R Q2 (elim_1 A R Q P P0 P1 P2)
           (t ⬝r t'⁻¹ʳ)}
      idpath (ap_con (simple_two_quotient.elim R Q2 P0 P1 (elim_1 A R Q P P0 P1 P2))
                     (inclt t) (inclt t')⁻¹ ⬝
             (simple_two_quotient.elim_inclt R Q2 (elim_1 A R Q P P0 P1 P2) t ◾
             (ap_inv (simple_two_quotient.elim R Q2 P0 P1 (elim_1 A R Q P P0 P1 P2))
                     (inclt t') ⬝
             inverse2 (simple_two_quotient.elim_inclt R Q2 (elim_1 A R Q P P0 P1 P2) t')))),▸*],
    rewrite [-con.assoc _ _ (con_inv_eq_idp _),-con.assoc _ _ (_ ◾ _),con.assoc _ _ (ap_con _ _ _),
             con.left_inv,↑whisker_left,con2_con_con2,-con.assoc (ap_inv _ _)⁻¹,
             con.left_inv,+idp_con,eq_of_con_inv_eq_idp_con2],
    xrewrite [to_left_inv !eq_equiv_con_inv_eq_idp (P2 q)],
    apply top_deg_square
  end

end
end two_quotient

--attribute two_quotient.j [constructor] --TODO
attribute /-two_quotient.rec-/ two_quotient.elim [unfold 8] [recursor 8]
--attribute two_quotient.elim_type [unfold 9]
attribute /-two_quotient.rec_on-/ two_quotient.elim_on [unfold 5]
--attribute two_quotient.elim_type_on [unfold 6]
