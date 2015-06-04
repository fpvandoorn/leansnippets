/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn

Quotient of a reflexive relation
-/

import .circle types.squareover

open type_quotient eq equiv equiv.ops option function circle

section
variables {A B : Type} (f : A → B) {a : A} {b : B}

definition ap_eq_idp_of_contractible (H : Πa, f a = b) (p : a = a) : ap f p = idp :=
begin
  apply @cancel_right _ _ _ _ _ _ (H a),
  rewrite [ap_con_eq_con_ap,ap_constant,idp_con]
end

end

-- this method seems to only work for pointed types A. We might want to let B be
-- A + A, where there is an aux point for every instance of sρ

namespace refl_quotient
section

  universe variables u v
  parameters {A : Type.{u}} (R : A → A → Type.{v}) (ρ : Πa, R a a)
  local abbreviation B := option A
  inductive pre_refl_rel : B → B → Type :=
  | Rmk' : Π{a a' : A}, R a a' → pre_refl_rel (some a) (some a')
  open pre_refl_rel
  local abbreviation R' := pre_refl_rel
  local abbreviation C := type_quotient R'

  definition pre_refl_quotient_f (a : A) (x : circle) : C :=
  circle.elim_on x (!class_of (some a)) (!eq_of_rel (Rmk' !ρ))
  local abbreviation f := pre_refl_quotient_f

  inductive refl_rel : C → C → Type :=
  | Rmk {} : Π(a : A) (x : circle), refl_rel (f a x) (!class_of none)
  open refl_rel
  local abbreviation S := refl_rel

  definition refl_quotient : Type := type_quotient S -- TODO: define this in root namespace
  local abbreviation D := refl_quotient

  definition rclass_of (a : A) : D := !class_of (!class_of (some a))
  definition req_of_rel {a a' : A} (H : R a a') : rclass_of a = rclass_of a' :=
  ap !class_of (!eq_of_rel (Rmk' H))

  definition pρ (a : A) : req_of_rel (ρ a) = idp :=
  assert H : Π (a' : A), ap (class_of S ∘ f a') loop = idp, from
    λa', ap_eq_idp_of_contractible (class_of S ∘ f a') (λx, eq_of_rel S (Rmk a' x)) loop,
  by rewrite [-H,ap_compose,↑f,↑pre_refl_quotient_f,↑circle.elim_on,elim_loop]

  definition sρ (a : A) : square (req_of_rel (ρ a)) idp idp idp :=
  square_of_eq !pρ
exit
  protected definition rec {P : refl_quotient → Type}
    (Pc : Π(a : A), P (rclass_of a))
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a =[req_of_rel H] Pc a')
    (Pr : Π(a : A), squareover P (sρ a) !Pp idpo idpo idpo)
    (x : refl_quotient) : P x :=
  begin
    induction x,
    { induction a,
      { cases a,
        { },
        { }},
      { }},
    { },
  end
exit
  protected definition rec_on [reducible] {P : pushout → Type} (y : pushout)
    (Pinl : Π(x : BL), P (inl x)) (Pinr : Π(x : TR), P (inr x))
    (Pglue : Π(x : TL), glue x ▸ Pinl (f x) = Pinr (g x)) : P y :=
  rec Pinl Pinr Pglue y

  theorem rec_glue {P : pushout → Type} (Pinl : Π(x : BL), P (inl x))
    (Pinr : Π(x : TR), P (inr x)) (Pglue : Π(x : TL), glue x ▸ Pinl (f x) = Pinr (g x))
      (x : TL) : apd (rec Pinl Pinr Pglue) (glue x) = Pglue x :=
  !rec_eq_of_rel

  protected definition elim {P : Type} (Pinl : BL → P) (Pinr : TR → P)
    (Pglue : Π(x : TL), Pinl (f x) = Pinr (g x)) (y : pushout) : P :=
  rec Pinl Pinr (λx, !tr_constant ⬝ Pglue x) y

  protected definition elim_on [reducible] {P : Type} (y : pushout) (Pinl : BL → P)
    (Pinr : TR → P) (Pglue : Π(x : TL), Pinl (f x) = Pinr (g x)) : P :=
  elim Pinl Pinr Pglue y

  theorem elim_glue {P : Type} (Pinl : BL → P) (Pinr : TR → P)
    (Pglue : Π(x : TL), Pinl (f x) = Pinr (g x)) (x : TL)
    : ap (elim Pinl Pinr Pglue) (glue x) = Pglue x :=
  begin
    apply (@cancel_left _ _ _ _ (tr_constant (glue x) (elim Pinl Pinr Pglue (inl (f x))))),
    rewrite [-apd_eq_tr_constant_con_ap,↑elim,rec_glue],
  end

  protected definition elim_type (Pinl : BL → Type) (Pinr : TR → Type)
    (Pglue : Π(x : TL), Pinl (f x) ≃ Pinr (g x)) (y : pushout) : Type :=
  elim Pinl Pinr (λx, ua (Pglue x)) y

  protected definition elim_type_on [reducible] (y : pushout) (Pinl : BL → Type)
    (Pinr : TR → Type) (Pglue : Π(x : TL), Pinl (f x) ≃ Pinr (g x)) : Type :=
  elim_type Pinl Pinr Pglue y

  theorem elim_type_glue (Pinl : BL → Type) (Pinr : TR → Type)
    (Pglue : Π(x : TL), Pinl (f x) ≃ Pinr (g x)) (x : TL)
    : transport (elim_type Pinl Pinr Pglue) (glue x) = Pglue x :=
  by rewrite [tr_eq_cast_ap_fn,↑elim_type,elim_glue];apply cast_ua_fn

end
end pushout

attribute pushout.inl pushout.inr [constructor]
attribute pushout.elim pushout.rec [unfold-c 10] [recursor 10]
attribute pushout.elim_type [unfold-c 9]
attribute pushout.rec_on pushout.elim_on [unfold-c 7]
attribute pushout.elim_type_on [unfold-c 6]
