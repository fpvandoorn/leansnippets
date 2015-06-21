/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn
-/

import hit.circle .disc

open quotient eq circle sum sigma equiv

namespace two_quotient

  section
  parameters {A : Type}
             (R : A → A → Type)
             (Q : Π⦃a⦄, R a a → Type)
  variables {a a' : A} {r : R a a} {s : R a a'}

  local abbreviation B := A ⊎ Σ(a : A) (r : R a a), Q r

  inductive pre_two_quotient_rel : B → B → Type :=
  | pre_Rmk {} : Π⦃a a'⦄ (r : R a a'), pre_two_quotient_rel (inl a) (inl a')
  --BUG: if {} not provided, the alias for incl is wrong

  definition pre_two_quotient := quotient pre_two_quotient_rel

  -- open pre_two_quotient_rel
  -- definition b [constructor] : pre_two_quotient := class_of pre_two_quotient_rel tt
  -- definition e [constructor] : pre_two_quotient := class_of pre_two_quotient_rel ff
  -- definition l : b = b    := eq_of_rel pre_two_quotient_rel Rl
  -- definition f [unfold-c 1] : S¹ → pre_two_quotient :=
  -- circle.elim b l

  open pre_two_quotient_rel
  local abbreviation C := quotient pre_two_quotient_rel
  private definition j [constructor] (a : A) : C := class_of pre_two_quotient_rel (inl a)
  private definition pre_aux [constructor] (q : Q r) : C :=
  class_of pre_two_quotient_rel (inr ⟨a, r, q⟩)
  private definition e (s : R a a') : j a = j a' := eq_of_rel _ (pre_Rmk s)
  private definition f [unfold-c 1] (q : Q r) : S¹ → C :=
  circle.elim (j a) (e r)

  private definition pre_rec [unfold-c 8] {P : C → Type}
    (Pj : Πa, P (j a)) (Pa : Π⦃a : A⦄ ⦃r : R a a⦄ (q : Q r), P (pre_aux q))
    (Pe : Π⦃a a' : A⦄ (s : R a a'), Pj a =[e s] Pj a') (x : C) : P x :=
  begin
    induction x with p,
    { induction p,
      { apply Pj},
      { induction a with a1 a2, induction a2, apply Pa}},
    { induction H, esimp, apply Pe},
  end

  private definition pre_elim [unfold-c 8] {P : Type} (Pj : A → P)
    (Pa : Π⦃a : A⦄ ⦃r : R a a⦄, Q r → P) (Pe : Π⦃a a' : A⦄ (s : R a a'), Pj a = Pj a') (x : C)
    : P :=
  pre_rec Pj Pa (λa a' s, pathover_of_eq (Pe s)) x

  private theorem rec_e {P : C → Type}
    (Pj : Πa, P (j a)) (Pa : Π⦃a : A⦄ ⦃r : R a a⦄ (q : Q r), P (pre_aux q))
    (Pe : Π⦃a a' : A⦄ (s : R a a'), Pj a =[e s] Pj a') ⦃a a' : A⦄ (s : R a a')
    : apdo (pre_rec Pj Pa Pe) (e s) = Pe s :=
  !rec_eq_of_rel

  private theorem elim_e {P : Type} (Pj : A → P) (Pa : Π⦃a : A⦄ ⦃r : R a a⦄, Q r → P)
    (Pe : Π⦃a a' : A⦄ (s : R a a'), Pj a = Pj a') ⦃a a' : A⦄ (s : R a a')
    : ap (pre_elim Pj Pa Pe) (e s) = Pe s :=
  begin
    apply eq_of_fn_eq_fn_inv !(pathover_constant (e s)),
    rewrite [▸*,-apdo_eq_pathover_of_eq_ap,↑pre_elim,rec_e],
  end

  inductive two_quotient_rel : C → C → Type :=
  | Rmk {} : Π{a : A} {r : R a a} (q : Q r) (x : circle), two_quotient_rel (f q x) (pre_aux q)

  open two_quotient_rel
  definition two_quotient := quotient two_quotient_rel
  local abbreviation D := two_quotient
  local abbreviation i [constructor] := class_of two_quotient_rel
  definition incl0 [constructor] (a : A) : D := i (j a)
  definition aux [constructor] (q : Q r) : D := i (pre_aux q)
  definition incl1 (s : R a a') : incl0 a = incl0 a' := ap i (e s)
  definition incl2' (q : Q r) (x : S¹) : i (f q x) = aux q :=
  eq_of_rel two_quotient_rel (Rmk q x)

  definition incl2 (q : Q r) : incl1 r = idp :=
  (ap02 i (elim_loop (j a) (e r))⁻¹) ⬝
  (ap_compose i (f q) loop)⁻¹ ⬝
  ap_weakly_constant (incl2' q) loop ⬝
  !con.right_inv

  local attribute f two_quotient i incl0 aux incl1 incl2' [reducible]

  protected definition elim [unfold-c 8] {P : Type} (P0 : A → P)
    (P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a') (P2 : Π⦃a : A⦄ ⦃r : R a a⦄ (q : Q r), P1 r = idp)
    (x : D) : P :=
  begin
    induction x,
    { refine (pre_elim _ _ _ a),
      { exact P0},
      { intro a r q, exact P0 a},
      { exact P1}},
    { exact abstract begin induction H, induction x,
      { exact idpath (P0 a)},
      { unfold f, apply pathover_eq, apply hdeg_square,
        exact abstract ap_compose (pre_elim P0 _ P1) (f q) loop ⬝
              ap _ !elim_loop ⬝
              !elim_e ⬝
              P2 q ⬝
              !ap_constant⁻¹ end} end end},
  end

  local attribute two_quotient.elim [reducible]

  definition elim_incl1 {P : Type} (P0 : A → P)
    (P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a') (P2 : Π⦃a : A⦄ ⦃r : R a a⦄ (q : Q r), P1 r = idp)
    ⦃a a' : A⦄ (s : R a a') : ap (elim P0 P1 P2) (incl1 s) = P1 s :=
  !ap_compose⁻¹ ⬝ !elim_e

  definition elim_incl2'_incl0 {P : Type} (P0 : A → P)
    (P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a') (P2 : Π⦃a : A⦄ ⦃r : R a a⦄ (q : Q r), P1 r = idp)
    ⦃a : A⦄ ⦃r : R a a⦄ (q : Q r) : ap (elim P0 P1 P2) (incl2' q base) = idpath (P0 a) :=
  !elim_eq_of_rel

  definition elim_incl2 {P : Type} (P0 : A → P)
    (P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a') (P2 : Π⦃a : A⦄ ⦃r : R a a⦄ (q : Q r), P1 r = idp)
    : square (ap02 (two_quotient.elim P0 P1 P2) incl2) P2 (elim_incl1 P) idp :=
  begin
    esimp [incl2,ap02],
    rewrite [+ap_con (ap _),▸*,-ap_compose (ap _) (ap i),+ap_inv],
    xrewrite [eq_top_of_square
               ((ap_compose_natural (two_quotient.elim Pb Pl Pf) i (elim_loop b l))⁻¹ʰ⁻¹ᵛ ⬝h
               (ap_ap_compose (two_quotient.elim Pb Pl Pf) i f loop)⁻¹ʰ⁻¹ᵛ ⬝h
               ap_ap_weakly_constant (two_quotient.elim Pb Pl Pf) incl2' loop ⬝h
               ap_con_right_inv_sq (two_quotient.elim Pb Pl Pf) (incl2' circle.incl0)),
               ↑[elim_incl1]],
    apply whisker_tl,
    rewrite [ap_weakly_constant_eq,naturality_apdo_eq (λx, !elim_eq_of_rel) loop,▸*,↑elim_2,rec_loop,
            square_of_pathover_concato_eq,square_of_pathover_eq_concato,
            eq_of_square_vconcat_eq,eq_of_square_eq_vconcat],
    --rewriting here with
    --    to_right_inv !pathover_eq_equiv_square (hdeg_square (elim_1 P Pb Pl Pf))
    -- takes ~11 seconds
    apply eq_vconcat,
    { apply ap (λx, _ ⬝ eq_con_inv_of_con_eq ((_ ⬝ x ⬝ _)⁻¹ ⬝ _) ⬝ _),
      transitivity _, apply ap eq_of_square,
        apply to_right_inv !pathover_eq_equiv_square (hdeg_square (elim_1 P Pb Pl Pf)),
      transitivity _, apply eq_of_square_hdeg_square,
      unfold elim_1, reflexivity},
    rewrite [+con_inv,whisker_left_inv,+inv_inv,-whisker_right_inv,
             con.assoc (whisker_left _ _),con.assoc _ (whisker_right _ _),▸*,
             whisker_right_con_whisker_left _ !ap_constant],
    xrewrite [-con.assoc _ _ (whisker_right _ _)],
    rewrite [con.assoc _ _ (whisker_left _ _),idp_con_whisker_left,▸*,
             con.assoc _ !ap_constant⁻¹,con.left_inv],
    xrewrite [eq_con_inv_of_con_eq_whisker_left,▸*],
    rewrite [+con.assoc _ _ !con.right_inv,right_inv_eq_idp (elim_incl2'_incl0 Pf),↑[whisker_left]],
    xrewrite [con2_con_con2],
    rewrite [idp_con,↑elim_incl2'_incl0,con.left_inv,whisker_right_inv,↑whisker_right],
    xrewrite [con.assoc _ _ (_ ◾ _)],
    rewrite [con.left_inv,▸*,-+con.assoc,con.assoc _⁻¹,↑[two_quotient.elim,function.compose],con.left_inv,
             ▸*,↑b,con.left_inv,idp_con],
    apply square_of_eq, reflexivity
  end


end two_quotient
