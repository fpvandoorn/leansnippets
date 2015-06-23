/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn

Declaration of the torus
-/

import .two_quotient_ext

open two_quotient eq bool unit

namespace torus

  definition torus_R (x y : unit.{0}) := bool
  local infix `⬝r`:75 := @e_closure.trans unit.{0} torus_R star star star
  local postfix `⁻¹ʳ`:(max+10) := @e_closure.symm unit.{0} torus_R star star
  local notation `[`:max a `]`:0 := @e_closure.of_rel unit.{0} torus_R star star a

  inductive torus_Q : Π⦃x : unit.{0}⦄, e_closure torus_R x x → Type :=
  | Qmk : torus_Q ([ff] ⬝r [tt] ⬝r ([tt] ⬝r [ff])⁻¹ʳ)

  definition torus := two_quotient torus_R torus_Q
  definition base  : torus := incl0 _ _ star
  definition loop1 : base = base := incl1 _ _ ff
  definition loop2 : base = base := incl1 _ _ tt
  definition surf  : loop1 ⬝ loop2 ⬝ (loop2 ⬝ loop1)⁻¹ = idp :=
  incl2 _ _ torus_Q.Qmk

  protected definition elim {P : Type} (Pb : P) (Pl1 : Pb = Pb) (Pl2 : Pb = Pb)
    (Ps : Pl1 ⬝ Pl2 ⬝ (Pl2 ⬝ Pl1)⁻¹ = idp) (x : torus) : P :=
  begin
    induction x,
    { exact Pb},
    { induction s,
      { exact Pl1},
      { exact Pl2}},
    { induction q, exact Ps},
  end

  definition elim_loop1 {P : Type} (Pb : P) (Pl1 : Pb = Pb) (Pl2 : Pb = Pb)
    (Ps : Pl1 ⬝ Pl2 ⬝ (Pl2 ⬝ Pl1)⁻¹ = idp) : ap (torus.elim Pb Pl1 Pl2 Ps) loop1 = Pl1 :=
  !elim_incl1

  definition elim_loop2 {P : Type} (Pb : P) (Pl1 : Pb = Pb) (Pl2 : Pb = Pb)
    (Ps : Pl1 ⬝ Pl2 ⬝ (Pl2 ⬝ Pl1)⁻¹ = idp) : ap (torus.elim Pb Pl1 Pl2 Ps) loop2 = Pl2 :=
  !elim_incl1

  definition elim_surf {P : Type} (Pb : P) (Pl1 : Pb = Pb) (Pl2 : Pb = Pb)
    (Ps : Pl1 ⬝ Pl2 ⬝ (Pl2 ⬝ Pl1)⁻¹ = idp)
  : square (ap02 (torus.elim Pb Pl1 Pl2 Ps) surf)
           Ps
           (!ap_con ⬝ ((!ap_con ⬝ (!elim_loop1 ◾ !elim_loop2)) ◾
                       (!ap_inv ⬝ inverse2 (!ap_con ⬝ (!elim_loop2 ◾ !elim_loop1)))))
           idp :=
  !elim_incl2


exit
  protected definition rec {P : torus → Type} (Pb : P base) (Pl1 : Pb =[loop1] Pb)
    (Pl2 : Pb =[loop2] Pb) (Pf : squareover P fill Pl1 Pl1 Pl2 Pl2)
    (x : torus) : P x :=
  begin
    induction x,
    { induction a,
      { exact Pb},
      { exact transport P (fill'' circle.base) Pb},
      { apply to_inv !(pathover_compose P), exact Pl1},
      { apply to_inv !(pathover_compose P), exact Pl2}},
    { cases H, clear a a',
      { esimp, induction x,
        { unfold f, apply pathover_tr},
        { /-apply pathover_pathover_fl,-/ apply sorry}}},
  end

  example {P : torus → Type} (Pb : P base) (Pl1 : Pb =[loop1] Pb) (Pl2 : Pb =[loop2] Pb)
          (Pf : squareover P fill Pl1 Pl1 Pl2 Pl2) : torus.rec Pb Pl1 Pl2 Pf base = Pb := idp

  definition rec_loop1 {P : torus → Type} (Pb : P base) (Pl1 : Pb =[loop1] Pb)
    (Pl2 : Pb =[loop2] Pb) (Pf : squareover P fill Pl1 Pl1 Pl2 Pl2)
    : apdo (torus.rec Pb Pl1 Pl2 Pf) loop1 = Pl1 :=
  sorry

  definition rec_loop2 {P : torus → Type} (Pb : P base) (Pl1 : Pb =[loop1] Pb)
    (Pl2 : Pb =[loop2] Pb) (Pf : squareover P fill Pl1 Pl1 Pl2 Pl2)
    : apdo (torus.rec Pb Pl1 Pl2 Pf) loop2 = Pl2 :=
  sorry

  definition rec_fill {P : torus → Type} (Pb : P base) (Pl1 : Pb =[loop1] Pb)
    (Pl2 : Pb =[loop2] Pb) (Pf : squareover P fill Pl1 Pl1 Pl2 Pl2)
    : cubeover P rfl1 (apds (torus.rec Pb Pl1 Pl2 Pf) fill) Pf
               (vdeg_squareover !rec_loop2) (vdeg_squareover !rec_loop2)
               (vdeg_squareover !rec_loop1) (vdeg_squareover !rec_loop1) :=
  sorry

end torus

exit
