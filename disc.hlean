/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Declaration of the disc
-/

import hit.circle types.cubical.cubeover types.cubical.pathover

open quotient eq function bool circle equiv

section
variables {A B : Type} {f : A → B} {a a' : A} {b b' : B}

definition ap_eq_idp_of_contractible (H : Πa, f a = b) (p : a = a) : ap f p = idp :=
begin
  apply @cancel_right _ _ _ _ _ _ (H a),
  rewrite [ap_con_eq_con_ap,ap_constant,idp_con]
end

definition eq2_of_circle_eq' {q : b' = b'} (H : Πx, circle.elim b' q x = b) (p : a = a) : q = idp :=
!elim_loop⁻¹ ⬝ (@cancel_right _ _ _ _ _ _ (H base)
  (ap_con_eq_con_ap H loop ⬝ ap (λx, _ ⬝ x) !ap_constant ⬝ !idp_con⁻¹))


definition eq2_of_circle_eq {q : a' = a'} (H : Πx, f (circle.elim a' q x) = b) (p : a = a)
  : ap f q = idp :=
ap (ap f) !elim_loop⁻¹ ⬝ !ap_compose⁻¹ ⬝ (@cancel_right _ _ _ _ _ _ (H base)
  (ap_con_eq_con_ap H loop ⬝ ap (λx, _ ⬝ x) !ap_constant ⬝ !idp_con⁻¹))

end


namespace disc

  inductive predisc_rel : bool → bool → Type :=
  | Rl : predisc_rel tt tt

  definition predisc := quotient predisc_rel

  namespace predisc
  open predisc_rel
  definition b [constructor] : predisc := class_of predisc_rel tt
  definition e [constructor] : predisc := class_of predisc_rel ff
  definition l : b = b    := eq_of_rel predisc_rel Rl
  definition f (x : S¹) : predisc :=
  circle.elim_on x b l

  protected definition rec [recursor] [unfold-c 5] {P : predisc → Type}
    (Pb : P b) (Pe : P e) (Pl : Pb =[l] Pb) (x : predisc) : P x :=
  begin
    induction x with c,
    { cases c, exact Pe, exact Pb},
    { cases H, exact Pl},
  end

  protected definition elim [recursor 5] [unfold-c 5] {P : Type}
    (Pb : P) (Pe : P) (Pl : Pb = Pb) (x : predisc) : P :=
  predisc.rec Pb Pe (pathover_of_eq Pl) x

  theorem rec_l {P : predisc → Type} (Pb : P b) (Pe : P e) (Pl : Pb =[l] Pb)
    : apdo (predisc.rec Pb Pe Pl) l = Pl :=
  !rec_eq_of_rel

  theorem elim_l {P : Type} (Pb : P) (Pe : P) (Pl : Pb = Pb)
    : ap (predisc.elim Pb Pe Pl) l = Pl :=
  begin
    apply eq_of_fn_eq_fn_inv !(pathover_constant l),
    rewrite [▸*,-apdo_eq_pathover_of_eq_ap,↑predisc.elim,rec_l],
  end

  end predisc
  open predisc

  inductive disc_rel : predisc → predisc → Type :=
  | Rf : Π(x : circle), disc_rel (f x) e
  open disc_rel

  definition disc := quotient disc_rel
  definition base  : disc := class_of disc_rel b
  definition aux   : disc := class_of disc_rel e
  definition lp : base = base := ap (class_of disc_rel) l
  definition fill' (x : S¹) : class_of disc_rel (f x) = aux := eq_of_rel disc_rel (Rf x)
  definition fill  : lp = idp :=
  eq2_of_circle_eq fill' l

    --,+ap_con at H, +ap_inv at H
    -- apply eq_con_of_con_inv_eq,
    -- rewrite [-idp_con loop2 at {2}],
    -- apply eq_con_of_con_inv_eq,



  -- definition heq_of_pathover {A : Type} {a a₂ : A} (B : A → Type) {p : a = a₂}
  -- {b : B a} {b₂ : B a₂} (q : b =[ p ] b₂) : b =[ ap B p ] b₂ :=
  -- pathover_ap _ _ q

  -- definition ap_eq {A B : Type} (f g : A → B) {a a' : A} (p : a = a') :
  --   ap (λx, f x = g x) p = ap011 eq (ap f p) (ap g p) :=
  -- by cases p;exact idp

  -- definition ap_eq_l {A B : Type} (f : A → B) {a a' : A} (p : a = a') (b : B) :
  --   ap (λx, f x = b) p = ap010 eq (ap f p) b :=
  -- by cases p;exact idp

  -- definition ap_eq_r {A B : Type} (f : A → B) {a a' : A} (p : a = a') (b : B) :
  --   ap (λx, b = f x) p = ap (eq b) (ap f p) :=
  -- by cases p;exact idp

  -- set_option pp.notation false
  -- set_option pp.implicit true
  protected definition elim {P : Type} (Pb : P) (Pl : Pb = Pb)
    (Pf : Pl = idp) (x : disc) : P :=
  begin
    induction x,
    { induction a,
      { exact Pb},
      { exact Pb},
      { exact Pl}},
    { cases H, clear a a', induction x,
        { reflexivity},
        { unfold f, apply pathover_eq,
          rewrite [ap_compose (circle.elim b l) (predisc.elim Pb Pb Pl),elim_loop,▸*,elim_l,ap_constant],
          apply hdeg_square, exact Pf}},
  end

  definition elim_lp {P : Type} (Pb : P) (Pl : Pb = Pb)
    (Pf : Pl = idp) : ap (disc.elim Pb Pl Pf) lp = Pl :=
  by unfold lp; exact !ap_compose⁻¹ ⬝ !elim_l
exit
  definition elim_fill {P : Type} (Pb : P) (Pl : Pb = Pb)
    (Pf : Pl = idp) : square (ap02 (disc.elim Pb Pl Pf) fill) Pf (elim_lp Pb Pl Pf) idp :=
  begin
    rewrite [↑[/-disc.elim,-/fill,fill']]
  end
exit
  protected definition rec {P : disc → Type} (Pb : P base) (Pl : Pb =[lp] Pb)
    (Pf : pathover _ Pl fill idpo)
    (x : disc) : P x :=
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

  example {P : disc → Type} (Pb : P base) (Pl1 : Pb =[loop1] Pb) (Pl2 : Pb =[loop2] Pb)
          (Pf : squareover P fill Pl1 Pl1 Pl2 Pl2) : disc.rec Pb Pl1 Pl2 Pf base = Pb := idp

  definition rec_loop1 {P : disc → Type} (Pb : P base) (Pl1 : Pb =[loop1] Pb)
    (Pl2 : Pb =[loop2] Pb) (Pf : squareover P fill Pl1 Pl1 Pl2 Pl2)
    : apdo (disc.rec Pb Pl1 Pl2 Pf) loop1 = Pl1 :=
  sorry

  definition rec_loop2 {P : disc → Type} (Pb : P base) (Pl1 : Pb =[loop1] Pb)
    (Pl2 : Pb =[loop2] Pb) (Pf : squareover P fill Pl1 Pl1 Pl2 Pl2)
    : apdo (disc.rec Pb Pl1 Pl2 Pf) loop2 = Pl2 :=
  sorry

  definition rec_fill {P : disc → Type} (Pb : P base) (Pl1 : Pb =[loop1] Pb)
    (Pl2 : Pb =[loop2] Pb) (Pf : squareover P fill Pl1 Pl1 Pl2 Pl2)
    : cubeover P rfl1 (apds (disc.rec Pb Pl1 Pl2 Pf) fill) Pf
               (vdeg_squareover !rec_loop2) (vdeg_squareover !rec_loop2)
               (vdeg_squareover !rec_loop1) (vdeg_squareover !rec_loop1) :=
  sorry

end disc

exit
