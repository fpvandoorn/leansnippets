/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn

Declaration of the torus
-/

import hit.circle types.cubical.cubeover

open quotient eq function bool circle equiv

section
variables {A B : Type} (f : A → B) {a : A} {b : B}

definition ap_eq_idp_of_contractible (H : Πa, f a = b) (p : a = a) : ap f p = idp :=
begin
  apply @cancel_right _ _ _ _ _ _ (H a),
  rewrite [ap_con_eq_con_ap,ap_constant,idp_con]
end


end

namespace torus

  -- definition tt (x : interval) : square := interval.elim_on x tl tr st
  -- definition bt (x : interval) : square := interval.elim_on x bl br sb
  -- definition lt (x : interval) : square := interval.elim_on x tl bl sl
  -- definition rt (x : interval) : square := interval.elim_on x tr br sr

  -- inductive torus_rel : square → square → Type :=
  -- | Rtb : Π(x : interval), torus_rel (tt x) (bt x)
  -- | Rlr : Π(x : interval), torus_rel (lt x) (rt x)
  -- open torus_rel
  --   definition torus := quotient torus_rel

  -- definition tl : torus := !class_of tl
  -- definition tr : torus := !class_of tr
  -- definition bl : torus := !class_of bl
  -- definition br : torus := !class_of br
  -- definition t : tl = tr := ap !class_of st
  -- definition b : bl = br := ap !class_of sb
  -- definition l : tl = bl := ap !class_of sl
  -- definition r : tr = br := ap !class_of sr

  -- definition t' : tl = tr := ap (!class_of ∘ tt) seg
  -- definition b' : bl = br := ap (!class_of ∘ bt) seg
  -- definition l' : tl = bl := ap (!class_of ∘ lt) seg
  -- definition r' : tr = br := ap (!class_of ∘ rt) seg

  -- definition surf : cubical.square t b l r := aps !class_of sfill
  -- definition t2 : tl = tr := !eq_of_rel (Rlr zero)
  -- definition b2 : bl = br := !eq_of_rel (Rlr one )
  -- definition l2 : tl = bl := !eq_of_rel (Rtb zero)
  -- definition r2 : tr = br := !eq_of_rel (Rtb one )
  -- definition surf2 : square t' b' l2 r2 :=
  -- square_of_homotopy' (λx, eq_of_rel torus_rel (Rtb x))  seg
  -- definition surf3 : square t2 b2 l' r' :=
  -- square_of_homotopy (λx, eq_of_rel torus_rel (Rlr x))  seg

  inductive pretorus_rel : bool → bool → Type :=
  | Rp : pretorus_rel tt tt
  | Rq : pretorus_rel tt tt

  definition pretorus := quotient pretorus_rel

  namespace pretorus
  open pretorus_rel
  definition b [constructor] : pretorus := class_of pretorus_rel tt
  definition e [constructor] : pretorus := class_of pretorus_rel ff
  definition p : b = b    := eq_of_rel pretorus_rel Rp
  definition q : b = b    := eq_of_rel pretorus_rel Rq
  definition f (x : S¹) : pretorus :=
  circle.elim_on x b (p ⬝ q ⬝ p⁻¹ ⬝ q⁻¹)

  protected definition rec [recursor] [unfold-c 6] {P : pretorus → Type}
    (Pb : P b) (Pe : P e) (Pp : Pb =[p] Pb) (Pq : Pb =[q] Pb) (x : pretorus) : P x :=
  begin
    induction x with c,
    { cases c, exact Pe, exact Pb},
    { cases H, exact Pp, exact Pq},
  end

  end pretorus
  open pretorus

  inductive torus_rel : pretorus → pretorus → Type :=
  | Rf : Π(x : circle), torus_rel (f x) e
  open torus_rel

  definition torus := quotient torus_rel
  definition base  : torus := class_of torus_rel b
  definition aux   : torus := class_of torus_rel e
  definition loop1 : base = base := ap (class_of torus_rel) p
  definition loop2 : base = base := ap (class_of torus_rel) q
  definition fill'' (x : S¹) : class_of torus_rel (f x) = aux := eq_of_rel torus_rel (Rf x)
  definition fill'  : loop1 ⬝ loop2 = loop2 ⬝ loop1 :=
  begin
    let H := ap_eq_idp_of_contractible (class_of torus_rel ∘ f) fill'' loop,
    rewrite [↑f at H, ap_compose at H, ↑circle.elim_on at H, circle.elim_loop at H,+ap_con at H,
             +ap_inv at H],
    apply eq_con_of_con_inv_eq,
    rewrite [-idp_con loop2 at {2}],
    apply eq_con_of_con_inv_eq,
    exact H
  end
  definition fill : square loop1 loop1 loop2 loop2 :=
  square_of_eq fill'

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
