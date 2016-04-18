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
  | Qrefl : Π(a : G), groupoid_quotient_Q [Rmk (ID a)] rfl
  | Qconcat : Π{a b c : G} (g : b ⟶ c) (f : a ⟶ b),
      groupoid_quotient_Q [Rmk (g ∘ f)] ([Rmk f] ⬝r [Rmk g])
  | Qinv : Π{a b : G} (f : a ⟶ b), groupoid_quotient_Q [Rmk f⁻¹] [Rmk f]⁻¹ʳ

  open groupoid_quotient_Q
  local abbreviation Q := groupoid_quotient_Q

  definition groupoid_quotient := trunc_two_quotient 1 R Q

  local attribute groupoid_quotient [reducible]
  definition is_trunc_groupoid_quotient [instance] : is_trunc 1 groupoid_quotient := _

  variables {a b c : G}
  definition elt (a : G) : groupoid_quotient := incl0 a
  definition pth (f : a ⟶ b) : elt a = elt b := incl1 (Rmk f)
  definition resp_id (a : G) : pth (ID a) = idp := incl2 (Qrefl a)
  definition resp_comp (g : b ⟶ c) (f : a ⟶ b) : pth (g ∘ f) = pth f ⬝ pth g := incl2 (Qconcat g f)
  definition resp_inv (f : a ⟶ b) : pth (f⁻¹) = (pth f)⁻¹ := incl2 (Qinv f)

  protected definition rec {P : groupoid_quotient → Type} [Πx, is_trunc 1 (P x)]
    (Pe : Πg, P (elt g)) (Pp : Π⦃a b⦄ (f : a ⟶ b), Pe a =[pth f] Pe b)
    (Pid : Πa, change_path (resp_id a) (Pp (ID a)) = idpo)
    (Pcomp : Π⦃a b c⦄ (g : b ⟶ c) (f : a ⟶ b),
      change_path (resp_comp g f) (Pp (g ∘ f)) = Pp f ⬝o Pp g)
    (Pinv : Π⦃a b⦄ (f : a ⟶ b), change_path (resp_inv f) (Pp f⁻¹) = (Pp f)⁻¹ᵒ)
    (x : groupoid_quotient) : P x :=
  begin
    induction x,
    { apply Pe},
    { induction s with a b f, apply Pp},
    { induction q with a a b c g f a b f,
      { apply Pid},
      { apply Pcomp},
      { apply Pinv}},
  end

  protected definition rec_on {P : groupoid_quotient → Type} [Πx, is_trunc 1 (P x)]
    (x : groupoid_quotient)
    (Pe : Πg, P (elt g)) (Pp : Π⦃a b⦄ (f : a ⟶ b), Pe a =[pth f] Pe b)
    (Pid : Πa, change_path (resp_id a) (Pp (ID a)) = idpo)
    (Pcomp : Π⦃a b c⦄ (g : b ⟶ c) (f : a ⟶ b),
      change_path (resp_comp g f) (Pp (g ∘ f)) = Pp f ⬝o Pp g)
    (Pinv : Π⦃a b⦄ (f : a ⟶ b), change_path (resp_inv f) (Pp f⁻¹) = (Pp f)⁻¹ᵒ) : P x :=
  rec Pe Pp Pid Pcomp Pinv x

  -- without the proof ... qed this takes 10+ seconds to compile
  definition rec_loop1 {P : groupoid_quotient → Type} [Πx, is_trunc 1 (P x)]
    {Pe : Πg, P (elt g)} {Pp : Π⦃a b⦄ (f : a ⟶ b), Pe a =[pth f] Pe b}
    (Pid : Πa, change_path (resp_id a) (Pp (ID a)) = idpo)
    (Pcomp : Π⦃a b c⦄ (g : b ⟶ c) (f : a ⟶ b),
      change_path (resp_comp g f) (Pp (g ∘ f)) = Pp f ⬝o Pp g)
    (Pinv : Π⦃a b⦄ (f : a ⟶ b), change_path (resp_inv f) (Pp f⁻¹) = (Pp f)⁻¹ᵒ)
    {a b : G} (f : a ⟶ b) : apd (rec Pe Pp Pid Pcomp Pinv) (pth f) = Pp f :=
  proof !rec_incl1 qed

  protected definition elim {P : Type} [is_trunc 1 P] (Pe : G → P)
    (Pp : Π⦃a b⦄ (f : a ⟶ b), Pe a = Pe b) (Pid : Πa, Pp (ID a) = idp)
    (Pcomp : Π⦃a b c⦄ (g : b ⟶ c) (f : a ⟶ b), Pp (g ∘ f) = Pp f ⬝ Pp g)
    (Pinv : Π⦃a b⦄ (f : a ⟶ b), Pp f⁻¹ = (Pp f)⁻¹) (x : groupoid_quotient) : P :=
  begin
    induction x,
    { exact Pe a},
    { induction s with a b f, exact Pp f},
    { induction q with a a b c g f a b f,
      { exact Pid a},
      { exact Pcomp g f},
      { exact Pinv f}},
  end

  protected definition elim_on [reducible] {P : Type} [is_trunc 1 P] (x : groupoid_quotient)
    (Pe : G → P) (Pp : Π⦃a b⦄ (f : a ⟶ b), Pe a = Pe b)
    (Pid : Πa, Pp (ID a) = idp)
    (Pcomp : Π⦃a b c⦄ (g : b ⟶ c) (f : a ⟶ b), Pp (g ∘ f) = Pp f ⬝ Pp g)
    (Pinv : Π⦃a b⦄ (f : a ⟶ b), Pp f⁻¹ = (Pp f)⁻¹) : P :=
  elim Pe @Pp Pid @Pcomp @Pinv x

  definition elim_pth {P : Type} [is_trunc 1 P] {Pe : G → P} {Pp : Π⦃a b⦄ (f : a ⟶ b), Pe a = Pe b}
    (Pid : Πa, Pp (ID a) = idp)
    (Pcomp : Π⦃a b c⦄ (g : b ⟶ c) (f : a ⟶ b), Pp (g ∘ f) = Pp f ⬝ Pp g)
    (Pinv : Π⦃a b⦄ (f : a ⟶ b), Pp f⁻¹ = (Pp f)⁻¹) {a b : G} (f : a ⟶ b) :
    ap (elim Pe Pp Pid Pcomp Pinv) (pth f) = Pp f :=
  !elim_incl1

  theorem elim_resp_id {P : Type} [is_trunc 1 P] {Pe : G → P}
    {Pp : Π⦃a b⦄ (f : a ⟶ b), Pe a = Pe b} (Pid : Πa, Pp (ID a) = idp)
    (Pcomp : Π⦃a b c⦄ (g : b ⟶ c) (f : a ⟶ b), Pp (g ∘ f) = Pp f ⬝ Pp g)
    (Pinv : Π⦃a b⦄ (f : a ⟶ b), Pp f⁻¹ = (Pp f)⁻¹) (a : G)
    : square (ap02 (elim Pe Pp Pid Pcomp Pinv) (resp_id a))
             (Pid a)
             (elim_pth Pid Pcomp Pinv (ID a))
             idp :=
  proof !elim_incl2 qed

  theorem elim_resp_comp {P : Type} [is_trunc 1 P] {Pe : G → P}
    {Pp : Π⦃a b⦄ (f : a ⟶ b), Pe a = Pe b} (Pid : Πa, Pp (ID a) = idp)
    (Pcomp : Π⦃a b c⦄ (g : b ⟶ c) (f : a ⟶ b), Pp (g ∘ f) = Pp f ⬝ Pp g)
    (Pinv : Π⦃a b⦄ (f : a ⟶ b), Pp f⁻¹ = (Pp f)⁻¹) {a b c : G} (g : b ⟶ c) (f : a ⟶ b)
    : square (ap02 (elim Pe Pp Pid Pcomp Pinv) (resp_comp g f))
             (Pcomp g f)
             (elim_pth Pid Pcomp Pinv (g ∘ f))
             (!ap_con ⬝ (elim_pth Pid Pcomp Pinv f ◾ elim_pth Pid Pcomp Pinv g)) :=
  proof !elim_incl2 qed

  theorem elim_resp_inv {P : Type} [is_trunc 1 P] {Pe : G → P}
    {Pp : Π⦃a b⦄ (f : a ⟶ b), Pe a = Pe b} (Pid : Πa, Pp (ID a) = idp)
    (Pcomp : Π⦃a b c⦄ (g : b ⟶ c) (f : a ⟶ b), Pp (g ∘ f) = Pp f ⬝ Pp g)
    (Pinv : Π⦃a b⦄ (f : a ⟶ b), Pp f⁻¹ = (Pp f)⁻¹) {a b : G} (f : a ⟶ b)
    : square (ap02 (elim Pe Pp Pid Pcomp Pinv) (resp_inv f))
             (Pinv f)
             (elim_pth Pid Pcomp Pinv f⁻¹)
             (!ap_inv ⬝ (elim_pth Pid Pcomp Pinv f)⁻²) :=
  proof !elim_incl2 qed

end
end groupoid_quotient

attribute groupoid_quotient.elt [constructor]
attribute groupoid_quotient.rec groupoid_quotient.elim [unfold 9] [recursor 9]
attribute groupoid_quotient.rec_on groupoid_quotient.elim_on [unfold 4]
