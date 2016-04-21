/-
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn

Eilenberg MacLane spaces
-/

import .groupoid_quotient homotopy.hopf
open algebra pointed nat eq category group algebra is_trunc iso pointed unit trunc equiv is_conn

namespace EM
  open groupoid_quotient
  -- TODO: redefine this in the groupoid file
  definition groupoid_of_group'.{l} [constructor] (A : Type.{l}) [G : group A] :
    groupoid.{0 l} unit :=
  begin
    fapply groupoid.mk; fapply precategory.mk: intros,
      { exact A},
      { exact _},
      { exact a_2 * a_1},
      { exact 1},
      { apply mul.assoc},
      { apply mul_one},
      { apply one_mul},
      { esimp [precategory.mk],
        fapply is_iso.mk,
        { exact f⁻¹},
        { apply mul.right_inv},
        { apply mul.left_inv}},
  end

  definition Groupoid_of_Group [constructor] (G : Group) : Groupoid :=
  Groupoid.mk unit (groupoid_of_group' G)

  variable {G : Group}
  definition EM1 (G : Group) : Type :=
  groupoid_quotient (Groupoid_of_Group G)
  definition pEM1 [constructor] (G : Group) : Type* :=
  pointed.MK (EM1 G) (elt star)

  definition base : EM1 G := elt star
  definition pth : G → base = base := pth
  definition resp_mul (g h : G) : pth (g * h) = pth g ⬝ pth h := resp_comp h g
  definition resp_one : pth (1 : G) = idp :=
  resp_id star

  definition resp_inv (g : G) : pth (g⁻¹) = (pth g)⁻¹ :=
  resp_inv g

  local attribute pointed.MK pointed.carrier pEM1 EM1 [reducible]
  protected definition rec {P : EM1 G → Type} [H : Π(x : EM1 G), is_trunc 1 (P x)]
    (Pb : P base) (Pp : Π(g : G), Pb =[pth g] Pb)
    (Pmul : Π(g h : G), change_path (resp_mul g h) (Pp (g * h)) = Pp g ⬝o Pp h) (x : EM1 G) : P x :=
  begin
    induction x,
    { induction g, exact Pb},
    { induction a, induction b, exact Pp f},
    { induction a, induction b, induction c, exact Pmul f g}
  end

  protected definition rec_on {P : EM1 G → Type} [H : Π(x : EM1 G), is_trunc 1 (P x)]
    (x : EM1 G) (Pb : P base) (Pp : Π(g : G), Pb =[pth g] Pb)
    (Pmul : Π(g h : G), change_path (resp_mul g h) (Pp (g * h)) = Pp g ⬝o Pp h) : P x :=
  EM.rec Pb Pp Pmul x

  protected definition set_rec {P : EM1 G → Type} [H : Π(x : EM1 G), is_set (P x)]
    (Pb : P base) (Pp : Π(g : G), Pb =[pth g] Pb) (x : EM1 G) : P x :=
  EM.rec Pb Pp !center x

  protected definition prop_rec {P : EM1 G → Type} [H : Π(x : EM1 G), is_prop (P x)]
    (Pb : P base) (x : EM1 G) : P x :=
  EM.rec Pb !center !center x

  definition rec_pth {P : EM1 G → Type} [H : Π(x : EM1 G), is_trunc 1 (P x)]
    {Pb : P base} {Pp : Π(g : G), Pb =[pth g] Pb}
    (Pmul : Π(g h : G), change_path (resp_mul g h) (Pp (g * h)) = Pp g ⬝o Pp h)
    (g : G) : apd (EM.rec Pb Pp Pmul) (pth g) = Pp g :=
  proof !rec_pth qed

  protected definition elim {P : Type} [is_trunc 1 P] (Pb : P) (Pp : Π(g : G), Pb = Pb)
    (Pmul : Π(g h : G), Pp (g * h) = Pp g ⬝ Pp h) (x : EM1 G) : P :=
  begin
    induction x,
    { exact Pb},
    { exact Pp f},
    { exact Pmul f g}
  end

  protected definition elim_on [reducible] {P : Type} [is_trunc 1 P] (x : EM1 G)
    (Pb : P) (Pp : G → Pb = Pb) (Pmul : Π(g h : G), Pp (g * h) = Pp g ⬝ Pp h) : P :=
  EM.elim Pb Pp Pmul x

  protected definition set_elim [reducible] {P : Type} [is_set P] (Pb : P) (Pp : G → Pb = Pb)
    (x : EM1 G) : P :=
  EM.elim Pb Pp !center x

  protected definition prop_elim [reducible] {P : Type} [is_prop P] (Pb : P) (x : EM1 G) : P :=
  EM.elim Pb !center !center x

  definition elim_pth {P : Type} [is_trunc 1 P] {Pb : P} {Pp : G → Pb = Pb}
    (Pmul : Π(g h : G), Pp (g * h) = Pp g ⬝ Pp h) (g : G) : ap (EM.elim Pb Pp Pmul) (pth g) = Pp g :=
  proof !elim_pth qed

  protected definition elim_set.{u} (Pb : Set.{u}) (Pp : Π(g : G), Pb ≃ Pb)
    (Pmul : Π(g h : G) (x : Pb), Pp (g * h) x = Pp h (Pp g x)) (x : EM1 G) : Set.{u} :=
  groupoid_quotient.elim_set (λu, Pb) (λu v, Pp) (λu v w g h, proof Pmul h g qed) x

  theorem elim_set_pth {Pb : Set} {Pp : Π(g : G), Pb ≃ Pb}
    (Pmul : Π(g h : G) (x : Pb), Pp (g * h) x = Pp h (Pp g x)) (g : G) :
    transport (EM.elim_set Pb Pp Pmul) (pth g) = Pp g :=
  !elim_set_pth

end EM

-- attribute EM.rec EM.elim [recursor 7]
attribute EM.base [constructor]
attribute EM.rec EM.elim [unfold 7] [recursor 7]
attribute EM.rec_on EM.elim_on [unfold 4]
attribute EM.set_rec EM.set_elim [unfold 6]
attribute EM.prop_rec EM.prop_elim EM.elim_set [unfold 5]

namespace EM
  open groupoid_quotient

  definition base_eq_base_equiv [constructor] (G : Group) : (base = base :> pEM1 G) ≃ G :=
  !elt_eq_elt_equiv

  definition fundamental_group_pEM1 (G : Group) : π₁ (pEM1 G) ≃g G :=
  begin
    fapply isomorphism_of_equiv,
    { exact trunc_equiv_trunc 0 !base_eq_base_equiv ⬝e trunc_equiv 0 G},
    { intros g h, induction g with p, induction h with q,
      exact encode_con p q}
  end

  proposition is_trunc_pEM1 [instance] (G : Group) : is_trunc 1 (pEM1 G) :=
  !is_trunc_groupoid_quotient

  proposition is_trunc_EM1 [instance] (G : Group) : is_trunc 1 (EM1 G) :=
  !is_trunc_groupoid_quotient

  proposition is_conn_EM1 [instance] (G : Group) : is_conn 0 (EM1 G) :=
  by apply @is_conn_groupoid_quotient; esimp; exact _

  -- use truncated Whitehead for this?
  definition equiv_EM1 {G : Group} {X : Type*} (e : Ω X ≃ G)
    (r : Πp q, e p * e q = e (p ⬝ q)) [is_conn 0 X] [is_trunc 1 X] : X ≃ pEM1 G :=
  begin
    fapply equiv.MK,
    { intro x, exact sorry},
    { intro x, induction x using EM.elim,
      { exact Point X},
      { note p := e⁻¹ᵉ g, exact p},
      { exact equiv.preserve_binary_of_inv_preserve e⁻¹ᵉ mul concat r g h}},
    { exact sorry},
    { exact sorry}
  end

  definition equiv_pEM1 {G : Group} {X : Type*} (e : π₁ X ≃g G) [is_conn 0 X] [is_trunc 1 X]
    : X ≃ pEM1 G :=
  sorry

end EM

open hopf
namespace EM
  -- The K(G,n+1):
  variables (G : CommGroup) (n : ℕ)

  definition EM1_mul [unfold 2 3] {G : CommGroup} (x x' : EM1 G) : EM1 G :=
  begin
    induction x,
    { exact x'},
    { induction x' using EM.set_rec,
      { exact pth g},
      { exact abstract begin apply loop_pathover, apply square_of_eq,
          refine !resp_mul⁻¹ ⬝ _ ⬝ !resp_mul,
          exact ap pth !mul.comm end end}},
    { refine EM.prop_rec _ x', esimp, apply resp_mul},
  end

  definition EM1_mul_one (G : CommGroup) (x : EM1 G) : EM1_mul x base = x :=
  begin
    induction x using EM.set_rec,
    { reflexivity},
    { apply eq_pathover_id_right, apply hdeg_square, refine EM.elim_pth _ g}
  end

  definition h_space_EM1 [constructor] [instance] (G : CommGroup) : h_space (EM1 G) :=
  begin
    fapply h_space.mk,
    { exact EM1_mul},
    { exact base},
    { intro x', reflexivity},
    { apply EM1_mul_one}
  end

  definition foo (G : CommGroup) : Ω[1] (ptrunc 2 (psusp (pEM1 G))) ≃ EM1 G :=
  begin
    do 2 esimp [iterated_ploop_space], apply hopf.delooping, reflexivity
  end

  definition bar (G : CommGroup) : Ω[2] (ptrunc 2 (psusp (pEM1 G))) ≃ G :=
  begin
    refine sorry
  end

end EM
