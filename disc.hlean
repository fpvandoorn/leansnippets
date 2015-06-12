/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Declaration of the disc
-/

import hit.circle types.cubical.cubeover types.cubical.pathover

open quotient eq function bool circle equiv

section
variables {A B C : Type} {f : A → B} {a a' : A} {b b' : B}

definition ap_eq_idp_of_contractible (H : Πa, f a = b) (p : a = a) : ap f p = idp :=
begin
  apply @cancel_right _ _ _ _ _ _ (H a),
  rewrite [ap_con_eq_con_ap,ap_constant,idp_con]
end

definition eq2_of_circle_eq' {q : b' = b'} (H : Πx, circle.elim b' q x = b) : q = idp :=
!elim_loop⁻¹ ⬝ (@cancel_right _ _ _ _ _ _ (H base)
  (ap_con_eq_con_ap H loop ⬝ ap (λx, _ ⬝ x) !ap_constant ⬝ !idp_con⁻¹))


definition eq2_of_circle_eq {q : a' = a'} (H : Πx, f (circle.elim a' q x) = b) : ap f q = idp :=
ap (ap f) !elim_loop⁻¹ ⬝
!ap_compose⁻¹ ⬝
(cancel_right --(H base)
  (ap_con_eq_con_ap H loop ⬝ ap (λx, _ ⬝ x) !ap_constant ⬝ !idp_con⁻¹))

-- definition eq2_of_circle_eq {q : a' = a'} (H : Πx, f (circle.elim a' q x) = b) : ap f q = idp :=
-- ap (ap f) !elim_loop⁻¹ ⬝
-- !ap_compose⁻¹ ⬝
-- begin check_expr square_of_pathover_eq (apdo H loop), check_expr ap_con_eq_con_ap H loop end ⬝
-- ap_constant loop _

-- check @ap_constant

definition ap02_eq2_of_circle_eq (g : B → C) {q : a' = a'} (H : Πx, f (circle.elim a' q x) = b)
 : square (eq2_of_circle_eq (λx, ap g (H x))) (ap02 g (eq2_of_circle_eq H)) !ap_compose idp :=
sorry

-- definition ap_con_eq_con_ap_loop /-{q : a' = a'} (H : Πx, f (circle.elim a' q x) = b)-/ (p) (q) :
--   ap_con_eq_con_ap (circle.rec p q) loop = q :=
-- sorry

-- definition eq2_of_circle_eq_circle_rec (g : B → C) {q : a' = a'} (H : Πx, f (circle.elim a' q x) = b) (p : f a' = b) (r : pathover (λx, f (circle.elim a' q x) = b) p loop p)
--  : square (eq2_of_circle_eq (circle.rec _ (pathover_eq (_)))) _ _ _ :=
-- sorry

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
  eq2_of_circle_eq fill'

  -- definition fill2' (x : S¹) : circle.elim base lp x = aux :=
  -- circle.rec_on x (eq_of_rel disc_rel (Rf circle.base)) (pathover_eq begin rewrite [ap_constant,elim_loop], apply square_of_eq, refine !idp_con⁻¹ ⬝ ap (λx, x ⬝ _) _, end )

  -- definition fill2  : lp = idp :=
  -- eq2_of_circle_eq' fill2'

    -- necesarry for proofs of fill/fill' in torus:
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
      { unfold f, apply pathover_eq, apply hdeg_square,
        exact ap_compose (circle.elim b l) (predisc.elim Pb Pb Pl) loop ⬝
              ap _ !elim_loop ⬝
              !elim_l ⬝
              Pf ⬝
              !ap_constant⁻¹}},
  end

  definition elim_lp {P : Type} (Pb : P) (Pl : Pb = Pb)
    (Pf : Pl = idp) : ap (disc.elim Pb Pl Pf) lp = Pl :=
  -- by unfold lp; refine !ap_compose⁻¹ ⬝ _
--  by unfold lp; refine !ap_compose⁻¹ ⬝ _;esimp [function.compose,disc.elim]
  by unfold lp; exact !ap_compose⁻¹ ⬝ !elim_l

  print disc.elim
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
