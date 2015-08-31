/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn

Declaration of the groupoid quotient
-/

import hit.two_quotient algebra.category.groupoid hit.trunc

open two_quotient eq bool unit relation category e_closure iso is_trunc trunc

namespace groupoid_quotient
section
  parameter (G : Groupoid)

  inductive groupoid_quotient_R : G → G → Type :=
  | Rmk : Π{a b : G} (f : a ⟶ b), groupoid_quotient_R a b
  -- local infix `⬝r`:75 := @e_closure.trans G groupoid_quotient_R
  -- local postfix `⁻¹ʳ`:(max+10) := @e_closure.symm G groupoid_quotient_R
  -- local notation `[`:max a `]`:0 := @e_closure.of_rel G groupoid_quotient_R _ _ a
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
  variables {a b c : G}
  definition groupoid_quotient := trunc 1 (two_quotient R Q)
  definition elt (a : G) : groupoid_quotient := tr (incl0 _ _ a)
  definition pth' (f : a ⟶ b) : incl0 _ _ a = incl0 _ _ b :=
  incl1 R Q (Rmk f)
  definition pth (f : a ⟶ b) : elt a = elt b := ap tr (pth' f)
  definition resp_id (a : G) : pth (ID a) = idp := ap02 tr (incl2 _ _ (Qrefl a))
  definition resp_comp (g : b ⟶ c) (f : a ⟶ b) : pth (g ∘ f) = pth f ⬝ pth g :=
  ap02 tr (incl2 _ _ (Qconcat g f)) ⬝ ap_con tr (pth' f) (pth' g)
  definition resp_inv (f : a ⟶ b) : pth (f⁻¹) = (pth f)⁻¹ :=
  ap02 tr (incl2 _ _ (Qinv f)) ⬝ ap_inv tr (pth' f)
  theorem is_trunc_groupoid_quotient : is_trunc 1 groupoid_quotient :=
  !is_trunc_trunc

  -- protected definition rec {P : groupoid_quotient → Type} (Pb : P base) (Pl1 : Pb =[loop1] Pb)
  --   (Pl2 : Pb =[loop2] Pb) (Pf : squareover P fill Pl1 Pl1 Pl2 Pl2)
  --   (x : groupoid_quotient) : P x :=
  -- sorry

  -- example {P : groupoid_quotient → Type} (Pb : P base) (Pl1 : Pb =[loop1] Pb) (Pl2 : Pb =[loop2] Pb)
  --         (Pf : squareover P fill Pl1 Pl1 Pl2 Pl2) : groupoid_quotient.rec Pb Pl1 Pl2 Pf base = Pb := idp

  -- definition rec_loop1 {P : groupoid_quotient → Type} (Pb : P base) (Pl1 : Pb =[loop1] Pb)
  --   (Pl2 : Pb =[loop2] Pb) (Pf : squareover P fill Pl1 Pl1 Pl2 Pl2)
  --   : apdo (groupoid_quotient.rec Pb Pl1 Pl2 Pf) loop1 = Pl1 :=
  -- sorry

  -- definition rec_loop2 {P : groupoid_quotient → Type} (Pb : P base) (Pl1 : Pb =[loop1] Pb)
  --   (Pl2 : Pb =[loop2] Pb) (Pf : squareover P fill Pl1 Pl1 Pl2 Pl2)
  --   : apdo (groupoid_quotient.rec Pb Pl1 Pl2 Pf) loop2 = Pl2 :=
  -- sorry

  -- definition rec_surf {P : groupoid_quotient → Type} (Pb : P base) (Pl1 : Pb =[loop1] Pb)
  --   (Pl2 : Pb =[loop2] Pb) (Pf : squareover P fill Pl1 Pl1 Pl2 Pl2)
  --   : cubeover P rfl1 (apds (groupoid_quotient.rec Pb Pl1 Pl2 Pf) fill) Pf
  --              (vdeg_squareover !rec_loop2) (vdeg_squareover !rec_loop2)
  --              (vdeg_squareover !rec_loop1) (vdeg_squareover !rec_loop1) :=
  -- sorry

  protected definition elim {P : 1-Type} (Pe : G → P) (Pp : Π⦃a b⦄ (f : a ⟶ b), Pe a = Pe b)
    (Pid : Πa, Pp (ID a) = idp) (Pcomp : Π⦃a b c⦄ (g : b ⟶ c) (f : a ⟶ b), Pp (g ∘ f) = Pp f ⬝ Pp g)
    (Pinv : Π⦃a b⦄ (f : a ⟶ b), Pp f⁻¹ = (Pp f)⁻¹) (x : groupoid_quotient) : P :=
  begin
    refine trunc.elim _ x,
    { intro x,
      induction x,
      { exact Pe a},
      { induction s with a b f, exact Pp f},
      { induction q, all_goals esimp [e_closure.elim],
        { exact Pid a},
        { exact Pcomp g f},
        { exact Pinv f}}}
  end

  protected definition elim_on [reducible] {P : 1-Type} (x : groupoid_quotient) (Pe : G → P)
    (Pp : Π⦃a b⦄ (f : a ⟶ b), Pe a = Pe b)
    (Pid : Πa, Pp (ID a) = idp) (Pcomp : Π⦃a b c⦄ (g : b ⟶ c) (f : a ⟶ b), Pp (g ∘ f) = Pp f ⬝ Pp g)
    (Pinv : Π⦃a b⦄ (f : a ⟶ b), Pp f⁻¹ = (Pp f)⁻¹) : P :=
  elim Pe @Pp Pid @Pcomp @Pinv x

  definition elim_pth {P : 1-Type} (Pe : G → P) (Pp : Π⦃a b⦄ (f : a ⟶ b), Pe a = Pe b)
    (Pid : Πa, Pp (ID a) = idp) (Pcomp : Π⦃a b c⦄ (g : b ⟶ c) (f : a ⟶ b), Pp (g ∘ f) = Pp f ⬝ Pp g)
    (Pinv : Π⦃a b⦄ (f : a ⟶ b), Pp f⁻¹ = (Pp f)⁻¹) {a b : G} (f : a ⟶ b) :
    ap (elim Pe Pp Pid Pcomp Pinv) (pth f) = Pp f :=
  !ap_compose⁻¹ ⬝ !elim_incl1

  -- set_option pp.notation false
  -- set_option pp.implicit true
  theorem elim_resp_id {P : 1-Type} (Pe : G → P) (Pp : Π⦃a b⦄ (f : a ⟶ b), Pe a = Pe b)
    (Pid : Πa, Pp (ID a) = idp) (Pcomp : Π⦃a b c⦄ (g : b ⟶ c) (f : a ⟶ b), Pp (g ∘ f) = Pp f ⬝ Pp g)
    (Pinv : Π⦃a b⦄ (f : a ⟶ b), Pp f⁻¹ = (Pp f)⁻¹) (a : G)
    : square (ap02 (elim Pe Pp Pid Pcomp Pinv) (resp_id a))
             (Pid a)
             !elim_pth
             idp :=
  begin
    rewrite [↑[groupoid_quotient.elim,elim_pth,resp_id,ap02],-ap_compose],
    -- let H := eq_top_of_square (natural_square ((ap_compose ((trunc.elim
    --             (two_quotient.elim R Q Pe @(groupoid_quotient_R.rec Pp)
    --                (groupoid_quotient_Q.rec Pid Pcomp Pinv))))
    --       (@tr 1 _))) (incl2 R Q (Qrefl a))),
    -- refine tr_rev (λx, square x _ _ _) _ _,
    -- rotate 1,
    -- exact eq_top_of_square (natural_square (λx, (ap_compose ((trunc.elim
    --             (two_quotient.elim R Q Pe @(groupoid_quotient_R.rec Pp)
    --                (groupoid_quotient_Q.rec Pid Pcomp Pinv))))
    --       (@tr 1 _) x)⁻¹) (incl2 R Q (Qrefl a))),

    -- xrewrite [eq_top_of_square (natural_square ((ap_compose ((trunc.elim
    --             (two_quotient.elim R Q Pe @(groupoid_quotient_R.rec Pp)
    --                (groupoid_quotient_Q.rec Pid Pcomp Pinv))))
    --       (@tr 1 _))) (incl2 R Q (Qrefl a)))],
    -- let H := eq_top_of_square
    --   (elim_incl2 R Q Pe @(groupoid_quotient_R.rec Pp) (groupoid_quotient_Q.rec Pid Pcomp Pinv) (Qrefl a)),
    xrewrite [eq_top_of_square (natural_square (homotopy.symm (ap_compose ((trunc.elim
                (two_quotient.elim R Q Pe @(groupoid_quotient_R.rec Pp)
                   (groupoid_quotient_Q.rec Pid Pcomp Pinv))))
          (@tr 1 _))) (incl2 R Q (Qrefl a)))],
    esimp [inclt,e_closure.elim,function.compose],
    xrewrite [eq_top_of_square (elim_incl2 R Q Pe @(groupoid_quotient_R.rec Pp)
                                 (groupoid_quotient_Q.rec Pid Pcomp Pinv) (Qrefl a))],
    esimp [elim_inclt]
  end
end
end groupoid_quotient

attribute groupoid_quotient.base [constructor]
attribute /-groupoid_quotient.rec-/ groupoid_quotient.elim [unfold 6] [recursor 6]
--attribute groupoid_quotient.elim_type [unfold 9]
attribute /-groupoid_quotient.rec_on-/ groupoid_quotient.elim_on [unfold 2]
--attribute groupoid_quotient.elim_type_on [unfold 6]
