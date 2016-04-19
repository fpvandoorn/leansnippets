/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn

Declaration of the groupoid quotient
-/

import algebra.category.groupoid hit.trunc .trunc_two_quotient

open trunc_two_quotient eq bool unit relation category e_closure iso is_trunc trunc

namespace groupoid_quotient
section
  parameter (G : Groupoid)

  inductive groupoid_quotient_R : G → G → Type :=
  | Rmk : Π{a b : G} (f : a ⟶ b), groupoid_quotient_R a b

  open groupoid_quotient_R
  local abbreviation R := groupoid_quotient_R

  inductive groupoid_quotient_Q : Π⦃x y : G⦄,
    e_closure groupoid_quotient_R x y → e_closure groupoid_quotient_R x y → Type :=
  | Qconcat : Π{a b c : G} (g : b ⟶ c) (f : a ⟶ b),
                groupoid_quotient_Q [Rmk (g ∘ f)] ([Rmk f] ⬝r [Rmk g])

  open groupoid_quotient_Q
  local abbreviation Q := groupoid_quotient_Q

  definition groupoid_quotient := trunc_two_quotient 1 R Q

  local attribute groupoid_quotient [reducible]
  definition is_trunc_groupoid_quotient [instance] : is_trunc 1 groupoid_quotient := _

  variables {a b c : G}
  definition elt (a : G) : groupoid_quotient := incl0 a
  definition pth (f : a ⟶ b) : elt a = elt b := incl1 (Rmk f)
  definition resp_comp (g : b ⟶ c) (f : a ⟶ b) : pth (g ∘ f) = pth f ⬝ pth g := incl2 (Qconcat g f)
  definition resp_id (a : G) : pth (ID a) = idp :=
  begin
    apply cancel_right (pth (id)), refine _ ⬝ !idp_con⁻¹,
    refine !resp_comp⁻¹ ⬝ _,
    exact ap pth !id_id,
  end

  definition resp_inv (f : a ⟶ b) : pth (f⁻¹) = (pth f)⁻¹ :=
  begin
    apply eq_inv_of_con_eq_idp',
    refine !resp_comp⁻¹ ⬝ _,
    refine ap pth !right_inverse ⬝ _,
    apply resp_id
  end

  protected definition rec {P : groupoid_quotient → Type} [Πx, is_trunc 1 (P x)]
    (Pe : Πg, P (elt g)) (Pp : Π⦃a b⦄ (f : a ⟶ b), Pe a =[pth f] Pe b)
    (Pcomp : Π⦃a b c⦄ (g : b ⟶ c) (f : a ⟶ b),
      change_path (resp_comp g f) (Pp (g ∘ f)) = Pp f ⬝o Pp g)
    (x : groupoid_quotient) : P x :=
  begin
    induction x,
    { apply Pe},
    { induction s with a b f, apply Pp},
    { induction q with a b c g f,
      apply Pcomp}
  end

  protected definition rec_on {P : groupoid_quotient → Type} [Πx, is_trunc 1 (P x)]
    (x : groupoid_quotient)
    (Pe : Πg, P (elt g)) (Pp : Π⦃a b⦄ (f : a ⟶ b), Pe a =[pth f] Pe b)
    (Pcomp : Π⦃a b c⦄ (g : b ⟶ c) (f : a ⟶ b),
      change_path (resp_comp g f) (Pp (g ∘ f)) = Pp f ⬝o Pp g) : P x :=
  rec Pe Pp Pcomp x

  definition rec_loop1 {P : groupoid_quotient → Type} [Πx, is_trunc 1 (P x)]
    {Pe : Πg, P (elt g)} {Pp : Π⦃a b⦄ (f : a ⟶ b), Pe a =[pth f] Pe b}
    (Pcomp : Π⦃a b c⦄ (g : b ⟶ c) (f : a ⟶ b),
      change_path (resp_comp g f) (Pp (g ∘ f)) = Pp f ⬝o Pp g)
    {a b : G} (f : a ⟶ b) : apd (rec Pe Pp Pcomp) (pth f) = Pp f :=
  proof !rec_incl1 qed

  protected definition elim {P : Type} [is_trunc 1 P] (Pe : G → P)
    (Pp : Π⦃a b⦄ (f : a ⟶ b), Pe a = Pe b)
    (Pcomp : Π⦃a b c⦄ (g : b ⟶ c) (f : a ⟶ b), Pp (g ∘ f) = Pp f ⬝ Pp g)
    (x : groupoid_quotient) : P :=
  begin
    induction x,
    { exact Pe a},
    { induction s with a b f, exact Pp f},
    { induction q with a b c g f,
      exact Pcomp g f}
  end

  protected definition elim_on [reducible] {P : Type} [is_trunc 1 P] (x : groupoid_quotient)
    (Pe : G → P) (Pp : Π⦃a b⦄ (f : a ⟶ b), Pe a = Pe b)
    (Pcomp : Π⦃a b c⦄ (g : b ⟶ c) (f : a ⟶ b), Pp (g ∘ f) = Pp f ⬝ Pp g) : P :=
  elim Pe Pp Pcomp x

  definition elim_pth {P : Type} [is_trunc 1 P] {Pe : G → P} {Pp : Π⦃a b⦄ (f : a ⟶ b), Pe a = Pe b}
    (Pcomp : Π⦃a b c⦄ (g : b ⟶ c) (f : a ⟶ b), Pp (g ∘ f) = Pp f ⬝ Pp g) {a b : G} (f : a ⟶ b) :
    ap (elim Pe Pp Pcomp) (pth f) = Pp f :=
  !elim_incl1

  -- The following rule is also true because P is a 1-type, and can be proven by `!is_set.elims`
  -- The following is the canonical proofs which holds for any truncated two-quotient.
  theorem elim_resp_comp {P : Type} [is_trunc 1 P] {Pe : G → P}
    {Pp : Π⦃a b⦄ (f : a ⟶ b), Pe a = Pe b}
    (Pcomp : Π⦃a b c⦄ (g : b ⟶ c) (f : a ⟶ b), Pp (g ∘ f) = Pp f ⬝ Pp g)
    {a b c : G} (g : b ⟶ c) (f : a ⟶ b)
    : square (ap02 (elim Pe Pp Pcomp) (resp_comp g f))
             (Pcomp g f)
             (elim_pth Pcomp (g ∘ f))
             (!ap_con ⬝ (elim_pth Pcomp f ◾ elim_pth Pcomp g)) :=
  proof !elim_incl2 qed

end
end groupoid_quotient

attribute groupoid_quotient.elt [constructor]
attribute groupoid_quotient.rec groupoid_quotient.elim [unfold 7] [recursor 7]
attribute groupoid_quotient.rec_on groupoid_quotient.elim_on [unfold 4]

open equiv is_equiv
namespace groupoid_quotient
  universe variables u v
  variables {G : Groupoid.{u v}} (g₁ g₂ : G)

--   print instances precategory
--   print instances groupoid

-- set_option pp.universes true
-- print homset
--   set_option pp.coercions true
  -- set_option pp.all true
--   definition precategory_Precategory_Groupoid [instance] (G : Groupoid)
--     : precategory (Groupoid._trans_of_to_Precategory_1 G) :=
--   _

  definition tua {n : ℕ₋₂} {A B : n-Type} (f : A ≃ B) : A = B :=
  to_inv (trunctype_eq_equiv n A B) (ua f)


  definition is_equiv_postcompose [constructor] {ob : Type} [precategory ob] {a b c : ob}
    (g : b ⟶ c) [is_iso g] : is_equiv (λ(f : a ⟶ b), g ∘ f) :=
  begin
    fapply adjointify,
    { exact λf', g⁻¹ ∘ f'},
    { intro f', apply comp_inverse_cancel_left},
    { intro f, apply inverse_comp_cancel_left}
  end

  definition equiv_postcompose [constructor] {ob : Type} [precategory ob] {a b c : ob}
    (g : b ⟶ c) [is_iso g] : (a ⟶ b) ≃ (a ⟶ c) :=
  equiv.mk (λ(f : a ⟶ b), g ∘ f) (is_equiv_postcompose g)

  include g₁

  protected definition code (y : groupoid_quotient G) : Set.{v} :=
  begin
    induction y with g₂ g₂ g₂' f,
    { exact homset g₁ g₂},
    { apply tua, esimp, exact equiv_postcompose f},
    { exact sorry}
  end

  definition path_space_groupoid_quotient : (elt G g₁ = elt G g₂) ≃ (g₁ ⟶ g₂) :=
  sorry

end groupoid_quotient
