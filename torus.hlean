/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn

Declaration of the torus
-/

import .two_quotient_ext

open two_quotient_ext eq two_quotient_ext.equiv_closure bool unit

namespace torus

  definition torus_R (x y : unit.{0}) := bool
  local infix `⬝r`:75 := @equiv_closure.trans unit.{0} torus_R star star star
  local postfix `⁻¹ʳ`:(max+10) := @equiv_closure.symm unit.{0} torus_R star star

  inductive torus_Q : Π⦃x : unit.{0}⦄, equiv_closure torus_R x x → Type :=
  | Qmk : torus_Q ((of_rel ff) ⬝r (of_rel tt) ⬝r (of_rel tt ⬝r of_rel ff)⁻¹ʳ)

  definition torus := two_quotient_ext torus_R torus_Q
  definition base  : torus := incl0 _ _ star
  definition loop1 : base = base := incl1 _ _ ff
  definition loop2 : base = base := incl1 _ _ tt
  set_option pp.implicit true
  definition fill  : loop1 ⬝ loop2 ⬝ (loop2 ⬝ loop1)⁻¹ = idp :=
  incl2 _ _ torus_Q.Qmk
exit
  set_option pp.notation false
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
