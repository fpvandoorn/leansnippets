/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Declaration of the reduced suspension
-/

import .two_quotient types.pointed

open two_quotient eq unit pointed

namespace red_susp
section

  parameter {A : Pointed}

  inductive red_susp_R : unit.{0} → unit.{0} → Type :=
  | Rmk : Π(a : A), red_susp_R star star
  open red_susp_R
  inductive red_susp_Q : Π⦃x : unit.{0}⦄, red_susp_R x x → Type :=
  | Qmk : red_susp_Q (Rmk pt)
  open red_susp_Q
  local abbreviation R := red_susp_R
  local abbreviation Q := red_susp_Q

  definition red_susp : Type := two_quotient R Q -- TODO: define this in root namespace

  definition base : red_susp :=
  incl0 R Q star

  definition merid (a : A) : base = base :=
  incl1 R Q (Rmk a)

  definition merid_pt : merid pt = idp :=
  incl2 R Q Qmk

  -- protected definition rec {P : pushout → Type} (Pinl : Π(x : BL), P (inl x))
  --   (Pinr : Π(x : TR), P (inr x)) (Pglue : Π(x : TL), Pinl (f x) =[glue x] Pinr (g x))
  --     (y : pushout) : P y :=
  -- begin
  --   induction y,
  --   { cases a,
  --       apply Pinl,
  --       apply Pinr},
  --   { cases H, apply Pglue}
  -- end

  -- protected definition rec_on [reducible] {P : pushout → Type} (y : pushout)
  --   (Pinl : Π(x : BL), P (inl x)) (Pinr : Π(x : TR), P (inr x))
  --   (Pglue : Π(x : TL), Pinl (f x) =[glue x] Pinr (g x)) : P y :=
  -- rec Pinl Pinr Pglue y

  -- theorem rec_glue {P : pushout → Type} (Pinl : Π(x : BL), P (inl x))
  --   (Pinr : Π(x : TR), P (inr x)) (Pglue : Π(x : TL), Pinl (f x) =[glue x] Pinr (g x))
  --     (x : TL) : apdo (rec Pinl Pinr Pglue) (glue x) = Pglue x :=
  -- !rec_eq_of_rel

  protected definition elim {P : Type} (Pb : P) (Pm : Π(a : A), Pb = Pb)
    (Pe : Pm pt = idp) (x : red_susp) : P :=
  two_quotient.elim _ _ (λy, Pb) (λa a' r, by induction r; exact Pm a)
                        (λa r q, begin induction q, exact Pe end) x

--UNEXPECTED BEHAVIOR IN THE FOLLOWING (wrong) TERM:
  protected definition remove_elim {P : Type} (Pb : P) (Pm : Π(a : A), Pb = Pb)
    (Pe : Pm pt = idp) (x : red_susp) : P :=
  two_quotient.elim _ _ (λy, Pb) (λa a' r, by induction r; exact Pm a)
                        (λa r q, Pe) x
-- expected behavior: error: no goals to solve.

  protected definition elim_on [reducible] {P : Type} (x : red_susp) (Pb : P)
    (Pm : Π(a : A), Pb = Pb) (Pe : Pm pt = idp) : P :=
  elim Pb Pm Pe x

  definition elim_merid {P : Type} {Pb : P} {Pm : Π(a : A), Pb = Pb}
    (Pe : Pm pt = idp) (a : A)
    : ap (elim Pb Pm Pe) (merid a) = Pm a :=
  !elim_incl1

  theorem elim_merid_pt {P : Type} (Pb : P) (Pm : Π(a : A), Pb = Pb)
    (Pe : Pm pt = idp) : square (ap02 (elim Pb Pm Pe) merid_pt) Pe (elim_merid Pe pt) idp :=
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
end red_susp

attribute red_susp.base [constructor]
attribute /-red_susp.rec-/ red_susp.elim [unfold-c 6] [recursor 6]
--attribute red_susp.elim_type [unfold-c 9]
attribute /-red_susp.rec_on-/ red_susp.elim_on [unfold-c 3]
--attribute red_susp.elim_type_on [unfold-c 6]
