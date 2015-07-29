/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn
-/

import hit.circle types.eq2

open quotient eq circle sum sigma equiv function

namespace two_quotient

  section
  parameters {A : Type}
             (R : A → A → Type)
             (Q : Π⦃a⦄, R a a → Type)
  variables {a a' : A} {r : R a a} {s : R a a'}

  local abbreviation B := A ⊎ Σ(a : A) (r : R a a), Q r

  inductive pre_two_quotient_rel : B → B → Type :=
  | pre_Rmk {} : Π⦃a a'⦄ (r : R a a'), pre_two_quotient_rel (inl a) (inl a')
  --BUG: if {} not provided, the alias for pre_Rmk is wrong

  definition pre_two_quotient := quotient pre_two_quotient_rel

  open pre_two_quotient_rel
  local abbreviation C := quotient pre_two_quotient_rel
  private definition j [constructor] (a : A) : C := class_of pre_two_quotient_rel (inl a)
  private definition pre_aux [constructor] (q : Q r) : C :=
  class_of pre_two_quotient_rel (inr ⟨a, r, q⟩)
  private definition e (s : R a a') : j a = j a' := eq_of_rel _ (pre_Rmk s)
  private definition f [unfold 7] (q : Q r) : S¹ → C :=
  circle.elim (j a) (e r)

  private definition pre_rec [unfold 8] {P : C → Type}
    (Pj : Πa, P (j a)) (Pa : Π⦃a : A⦄ ⦃r : R a a⦄ (q : Q r), P (pre_aux q))
    (Pe : Π⦃a a' : A⦄ (s : R a a'), Pj a =[e s] Pj a') (x : C) : P x :=
  begin
    induction x with p,
    { induction p,
      { apply Pj},
      { induction a with a1 a2, induction a2, apply Pa}},
    { induction H, esimp, apply Pe},
  end

  private definition pre_elim [unfold 8] {P : Type} (Pj : A → P)
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
  local abbreviation i := class_of two_quotient_rel
  definition incl0 (a : A) : D := i (j a)
  definition aux (q : Q r) : D := i (pre_aux q)
  definition incl1 (s : R a a') : incl0 a = incl0 a' := ap i (e s)
  definition incl2' (q : Q r) (x : S¹) : i (f q x) = aux q :=
  eq_of_rel two_quotient_rel (Rmk q x)

  definition incl2 (q : Q r) : incl1 r = idp :=
  (ap02 i (elim_loop (j a) (e r))⁻¹) ⬝
  (ap_compose i (f q) loop)⁻¹ ⬝
  ap_weakly_constant (incl2' q) loop ⬝
  !con.right_inv

  local attribute two_quotient f i incl0 aux incl1 incl2' [reducible]
  local attribute i aux incl0 [constructor]

  protected definition elim {P : Type} (P0 : A → P)
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
      { unfold f, apply eq_pathover, apply hdeg_square,
        exact abstract ap_compose (pre_elim P0 _ P1) (f q) loop ⬝
              ap _ !elim_loop ⬝
              !elim_e ⬝
              P2 q ⬝
              !ap_constant⁻¹ end} end end},
  end
  local attribute elim [unfold 8]

  protected definition elim_on {P : Type} (x : D) (P0 : A → P)
    (P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a') (P2 : Π⦃a : A⦄ ⦃r : R a a⦄ (q : Q r), P1 r = idp)
     : P :=
  elim P0 P1 P2 x

  definition elim_incl1 {P : Type} {P0 : A → P}
    {P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a'}
    (P2 : Π⦃a : A⦄ ⦃r : R a a⦄ (q : Q r), P1 r = idp)
    ⦃a a' : A⦄ (s : R a a') : ap (elim P0 P1 P2) (incl1 s) = P1 s :=
  !ap_compose⁻¹ ⬝ !elim_e

  definition elim_incl2'_incl0 {P : Type} {P0 : A → P}
    {P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a'}
    (P2 : Π⦃a : A⦄ ⦃r : R a a⦄ (q : Q r), P1 r = idp)
    ⦃a : A⦄ ⦃r : R a a⦄ (q : Q r) : ap (elim P0 P1 P2) (incl2' q base) = idpath (P0 a) :=
  !elim_eq_of_rel
--  set_option pp.implicit true
  theorem elim_incl2 {P : Type} (P0 : A → P)
    (P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a') (P2 : Π⦃a : A⦄ ⦃r : R a a⦄ (q : Q r), P1 r = idp)
    ⦃a : A⦄ ⦃r : R a a⦄ (q : Q r)
    : square (ap02 (elim P0 P1 P2) (incl2 q)) (P2 q) (elim_incl1 P2 r) idp :=
  begin
check_expr empty,
    esimp [incl2,ap02],
    rewrite [+ap_con (ap _),▸*,-ap_compose (ap _) (ap i),+ap_inv],
    xrewrite [eq_top_of_square
               ((ap_compose_natural (elim P0 P1 P2) i (elim_loop (j a) (e r)))⁻¹ʰ⁻¹ᵛ ⬝h
               (ap_ap_compose (elim P0 P1 P2) i (f q) loop)⁻¹ʰ⁻¹ᵛ ⬝h
               ap_ap_weakly_constant (elim P0 P1 P2) (incl2' q) loop ⬝h
               ap_con_right_inv_sq (elim P0 P1 P2) (incl2' q base)),
               ↑[elim_incl1]],
    apply whisker_tl,
check_expr empty,
    rewrite [ap_weakly_constant_eq],
    xrewrite [naturality_apdo_eq (λx, !elim_eq_of_rel) loop],
    rewrite [↑elim_2,rec_loop,square_of_pathover_concato_eq,square_of_pathover_eq_concato,
            eq_of_square_vconcat_eq,eq_of_square_eq_vconcat],
check_expr empty,
    apply eq_vconcat,
    { apply ap (λx, _ ⬝ eq_con_inv_of_con_eq ((_ ⬝ x ⬝ _)⁻¹ ⬝ _) ⬝ _),
      transitivity _, apply ap eq_of_square,
        apply to_right_inv !eq_pathover_equiv_square (hdeg_square (elim_1 P A R Q P0 P1 a r q P2)),
      transitivity _, apply eq_of_square_hdeg_square,
      unfold elim_1, reflexivity},
check_expr empty,
    rewrite [+con_inv,whisker_left_inv,+inv_inv,-whisker_right_inv,
             con.assoc (whisker_left _ _),con.assoc _ (whisker_right _ _),▸*,
             whisker_right_con_whisker_left _ !ap_constant],
    xrewrite [-con.assoc _ _ (whisker_right _ _)],
    rewrite [con.assoc _ _ (whisker_left _ _),idp_con_whisker_left,▸*,
             con.assoc _ !ap_constant⁻¹,con.left_inv],
    xrewrite [eq_con_inv_of_con_eq_whisker_left,▸*],
check_expr empty,
    rewrite [+con.assoc _ _ !con.right_inv,
             right_inv_eq_idp (
               (λ(x : ap (elim P0 P1 P2) (incl2' q base) = idpath
               (elim P0 P1 P2 (class_of two_quotient_rel (f q base)))), x)
                (elim_incl2'_incl0 P2 q)),
             ↑[whisker_left]],
    xrewrite [con2_con_con2],
    rewrite [idp_con,↑elim_incl2'_incl0,con.left_inv,whisker_right_inv,↑whisker_right],
    xrewrite [con.assoc _ _ (_ ◾ _)],
    rewrite [con.left_inv,▸*,-+con.assoc,con.assoc _⁻¹,↑[elim,function.compose],con.left_inv,
             ▸*,↑j,con.left_inv,idp_con],
check_expr empty,
    apply square_of_eq, reflexivity
  end

end
end two_quotient

attribute two_quotient.incl0 [constructor]
attribute /-two_quotient.rec-/ two_quotient.elim [unfold 8] [recursor 8]
--attribute two_quotient.elim_type [unfold 9]
attribute /-two_quotient.rec_on-/ two_quotient.elim_on [unfold 5]
--attribute two_quotient.elim_type_on [unfold 6]
