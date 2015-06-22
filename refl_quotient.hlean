/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn

Quotient of a reflexive relation
-/

import hit.circle types.cubical.squareover .two_quotient

open eq two_quotient

namespace refl_quotient
section

  parameters {A : Type} (R : A → A → Type) (ρ : Πa, R a a)
  inductive refl_quotient_Q : Π⦃a : A⦄, R a a → Type :=
  | Qmk {} : Π(a : A), refl_quotient_Q (ρ a)
  open refl_quotient_Q
  local abbreviation Q := refl_quotient_Q

  definition refl_quotient : Type := two_quotient R Q -- TODO: define this in root namespace

  definition rclass_of (a : A) : refl_quotient := incl0 R Q a
  definition req_of_rel ⦃a a' : A⦄ (r : R a a') : rclass_of a = rclass_of a' :=
  incl1 R Q r

  definition pρ (a : A) : req_of_rel (ρ a) = idp :=
  incl2 R Q (Qmk a)

  -- protected definition rec {P : refl_quotient → Type}
  --   (Pc : Π(a : A), P (rclass_of a))
  --   (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a =[req_of_rel H] Pc a')
  --   (Pr : Π(a : A), Pp (ρ a) =[pρ a] idpo)
  --   (x : refl_quotient) : P x :=
  -- sorry

  -- protected definition rec_on [reducible] {P : pushout → Type} (y : pushout)
  --   (Pinl : Π(x : BL), P (inl x)) (Pinr : Π(x : TR), P (inr x))
  --   (Pglue : Π(x : TL), glue x ▸ Pinl (f x) = Pinr (g x)) : P y :=
  -- rec Pinl Pinr Pglue y

  -- theorem rec_glue {P : pushout → Type} (Pinl : Π(x : BL), P (inl x))
  --   (Pinr : Π(x : TR), P (inr x)) (Pglue : Π(x : TL), glue x ▸ Pinl (f x) = Pinr (g x))
  --     (x : TL) : apd (rec Pinl Pinr Pglue) (glue x) = Pglue x :=
  -- !rec_eq_of_rel

  protected definition elim {P : Type} (Pc : Π(a : A), P)
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a = Pc a') (Pr : Π(a : A), Pp (ρ a) = idp)
    (x : refl_quotient) : P :=
  two_quotient.elim _ _ (λa, Pc a) (λa a' r, Pp r)
                        (λa r q, by induction q;apply Pr) x

  protected definition elim_on [reducible] {P : Type} (x : refl_quotient) (Pc : Π(a : A), P)
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a = Pc a') (Pr : Π(a : A), Pp (ρ a) = idp) : P :=
  elim Pc Pp Pr x

  definition elim_req_of_rel {P : Type} {Pc : Π(a : A), P}
    {Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a = Pc a'} (Pr : Π(a : A), Pp (ρ a) = idp)
    ⦃a a' : A⦄ (r : R a a') : ap (elim Pc Pp Pr) (req_of_rel r) = Pp r :=
  !elim_incl1

  theorem elim_pρ {P : Type} (Pc : Π(a : A), P)
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a = Pc a') (Pr : Π(a : A), Pp (ρ a) = idp) (a : A)
     : square (ap02 (elim Pc Pp Pr) (pρ a)) (Pr a) (elim_req_of_rel Pr (ρ a)) idp :=
  !elim_incl2

  -- protected definition elim_type (Pinl : BL → Type) (Pinr : TR → Type)
  --   (Pglue : Π(x : TL), Pinl (f x) ≃ Pinr (g x)) (y : pushout) : Type :=
  -- elim Pinl Pinr (λx, ua (Pglue x)) y

  -- protected definition elim_type_on [reducible] (y : pushout) (Pinl : BL → Type)
  --   (Pinr : TR → Type) (Pglue : Π(x : TL), Pinl (f x) ≃ Pinr (g x)) : Type :=
  -- elim_type Pinl Pinr Pglue y

  -- theorem elim_type_glue (Pinl : BL → Type) (Pinr : TR → Type)
  --   (Pglue : Π(x : TL), Pinl (f x) ≃ Pinr (g x)) (x : TL)
  --   : transport (elim_type Pinl Pinr Pglue) (glue x) = Pglue x :=
  -- by rewrite [tr_eq_cast_ap_fn,↑elim_type,elim_glue];apply cast_ua_fn

end
end refl_quotient

attribute refl_quotient.rclass_of [constructor]
attribute /-refl_quotient.rec-/ refl_quotient.elim [unfold-c 8] [recursor 8]
--attribute refl_quotient.elim_type [unfold-c 9]
attribute /-refl_quotient.rec_on-/ refl_quotient.elim_on [unfold-c 5]
--attribute refl_quotient.elim_type_on [unfold-c 6]
