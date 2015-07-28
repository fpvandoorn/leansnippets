/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn

Quotient of a reflexive relation
-/

import hit.circle types.cubical.squareover

open quotient eq equiv equiv.ops function circle sum

section
variables {A B : Type} (f : A → B) {a : A} {b : B}

definition ap_eq_idp_of_contractible (H : Πa, f a = b) (p : a = a) : ap f p = idp :=
begin
  apply @cancel_right _ _ _ _ _ _ (H a),
  rewrite [ap_con_eq_con_ap,ap_constant,idp_con]
end

end

/-
  The points are B := A + A. The (inl a) are the actual points, while the (inr a) are all
  auxilliary points as the base for the equality of ρ a
-/


namespace refl_quotient
section

  parameters {A : Type} (R : A → A → Type) (ρ : Πa, R a a)
  local abbreviation B := A + A
  inductive pre_refl_rel : B → B → Type :=
  | Rmk' : Π{a a' : A}, R a a' → pre_refl_rel (inl a) (inl a')
  open pre_refl_rel
  local abbreviation R' := pre_refl_rel
  local abbreviation C := quotient R'

  definition pre_refl_quotient_f (a : A) (x : circle) : C :=
  circle.elim_on x (!class_of (inl a)) (!eq_of_rel (Rmk' !ρ))
  local abbreviation f := pre_refl_quotient_f
  local attribute pre_refl_quotient_f f [unfold-c 5]
  inductive refl_rel : C → C → Type :=
  | Rmk {} : Π(a : A) (x : circle), refl_rel (f a x) (!class_of (inr a))
  open refl_rel
  local abbreviation S := refl_rel

  definition refl_quotient : Type := quotient S -- TODO: define this in root namespace

  definition rclass_of (a : A) : refl_quotient := !class_of (!class_of (inl a))
  definition req_of_rel {a a' : A} (H : R a a') : rclass_of a = rclass_of a' :=
  ap !class_of (!eq_of_rel (Rmk' H))

  protected definition aux (a : A) : refl_quotient := !class_of (!class_of (inr a))
  definition ρaux (a : A) (x : circle) : !class_of (f a x) = aux a := !eq_of_rel (Rmk a x)

  definition pρ (a : A) : req_of_rel (ρ a) = idp :=
  assert H : Π (a' : A), ap (class_of S ∘ f a') loop = idp, from
    λa', ap_eq_idp_of_contractible (class_of S ∘ f a') (ρaux a') loop,
  begin
    xrewrite [-H],
    rewrite [ap_compose,↑f,↑pre_refl_quotient_f,↑circle.elim_on,elim_loop]
  end

  definition sρ (a : A) : square (req_of_rel (ρ a)) idp idp idp :=
  square_of_eq !pρ

  --set_option pp.notation false
  protected definition rec {P : refl_quotient → Type}
    (Pc : Π(a : A), P (rclass_of a))
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a =[req_of_rel H] Pc a')
    (Pr : Π(a : A), Pp (ρ a) =[pρ a] idpo)
    (x : refl_quotient) : P x :=
/- fibration of pathover of Pr: (λ (p : rclass_of a = rclass_of a), pathover P (Pc a) p (Pc a)) -/
  begin
    induction x with c c c' H,
    { induction c with b b b' H,
      { cases b with a a,
          apply Pc,
          exact transport P (ρaux a base) (Pc a)},
      { cases H with a a' H, esimp, apply pathover_of_pathover_ap P, apply Pp}},
    { cases H, clear c c', esimp, induction x,
      { esimp, esimp, apply pathover_tr},
      { esimp, apply sorry/- fibration here:
(λ (x : circle),
       pathover P
         (quotient.rec
            (λ (b : sum A A), sum.cases_on b Pc (λ (a : A), transport P (ρaux a base) (Pc a)))
            (λ (b b' : sum A A) (H : R' b b'),
               pre_refl_rel.cases_on H
                 (λ (a a' : A) (H : R a a'), pathover_of_pathover_ap P (class_of S) (Pp H)))
            (f a x))
         (eq_of_rel S (Rmk a x))
         (transport P (ρaux a base) (Pc a)))
-/
}},
  end

  protected definition rec_on [reducible] {P : refl_quotient → Type} (x : refl_quotient)
    (Pc : Π(a : A), P (rclass_of a))
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a =[req_of_rel H] Pc a')
    (Pr : Π(a : A), Pp (ρ a) =[pρ a] idpo) : P x :=
  rec Pc Pp Pr x

  theorem rec_req_of_rel {P : refl_quotient → Type}
    (Pc : Π(a : A), P (rclass_of a))
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a =[req_of_rel H] Pc a')
    (Pr : Π(a : A), Pp (ρ a) =[pρ a] idpo)
    {a a' : A} (H : R a a') : apdo (rec Pc Pp Pr) (req_of_rel H) = Pp H :=
  sorry

  theorem rec_pρ {P : refl_quotient → Type}
    (Pc : Π(a : A), P (rclass_of a))
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a =[req_of_rel H] Pc a')
    (Pr : Π(a : A), Pp (ρ a) =[pρ a] idpo)
    (a : A) : sorry (rec Pc Pp Pr) (pρ a) = Pr a := --do we need patover/squareover here?
  sorry

end
end refl_quotient

attribute refl_quotient.rclass_of [constructor]
attribute refl_quotient.rec /-refl_quotient.elim-/ [unfold-c 8] [recursor 8]
-- attribute refl_quotient.elim_type [unfold-c 7]
attribute refl_quotient.rec_on /-refl_quotient.elim_on-/ [unfold-c 5]
-- attribute refl_quotient.elim_type_on [unfold-c 4]
