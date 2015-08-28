/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Declaration of the disc
-/

import hit.circle cubical.squareover eq2

open quotient eq function bool circle equiv

namespace disc

  inductive predisc_rel : bool → bool → Type :=
  | Rl : predisc_rel tt tt

  definition predisc := quotient predisc_rel

  namespace predisc
  open predisc_rel
  definition b [constructor] : predisc := class_of predisc_rel tt
  definition e [constructor] : predisc := class_of predisc_rel ff
  definition l : b = b    := eq_of_rel predisc_rel Rl
  definition f [unfold 1] : S¹ → predisc :=
  circle.elim b l


  protected definition rec [recursor] [unfold 5] {P : predisc → Type}
    (Pb : P b) (Pe : P e) (Pl : Pb =[l] Pb) (x : predisc) : P x :=
  begin
    induction x with c,
    { cases c, exact Pe, exact Pb},
    { cases H, exact Pl},
  end

  protected definition elim [recursor 5] [unfold 5] {P : Type}
    (Pb : P) (Pe : P) (Pl : Pb = Pb) (x : predisc) : P :=
  predisc.rec Pb Pe (pathover_of_eq Pl) x

  theorem rec_l {P : predisc → Type} (Pb : P b) (Pe : P e) (Pl : Pb =[l] Pb)
    : apdo (predisc.rec Pb Pe Pl) l = Pl :=
  !rec_eq_of_rel

  theorem elim_l {P : Type} {Pb Pe : P} (Pl : Pb = Pb)
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
  private definition i [constructor] : predisc → disc := class_of disc_rel
  definition base [constructor] : disc := i b
  definition aux  [constructor] : disc := i e
  definition lp : base = base := ap i l
  definition fill' (x : S¹) : i (f x) = aux := eq_of_rel disc_rel (Rf x)
  definition fill  : lp = idp :=
  (ap02 i (elim_loop b l)⁻¹) ⬝
  (ap_compose i f loop)⁻¹ ⬝
  ap_weakly_constant fill' loop ⬝
  !con.right_inv

  local attribute disc f i base aux lp fill' [reducible]

  protected definition elim [unfold 5] {P : Type} (Pb : P) (Pl : Pb = Pb)
    (Pf : Pl = idp) (x : disc) : P :=
  begin
    induction x,
    { induction a,
      { exact Pb},
      { exact Pb},
      { exact Pl}},
    { exact abstract begin induction H, induction x,
      { exact idpath Pb},
      { unfold f, apply eq_pathover, apply hdeg_square,
        exact abstract ap_compose (predisc.elim Pb Pb Pl) f loop ⬝
              ap _ !elim_loop ⬝
              !elim_l ⬝
              Pf ⬝
              !ap_constant⁻¹ end} end end},
  end

  local attribute disc.elim [reducible]

  definition elim_lp {P : Type} {Pb : P} {Pl : Pb = Pb}
    (Pf : Pl = idp) : ap (disc.elim Pb Pl Pf) lp = Pl :=
  !ap_compose⁻¹ ⬝ !elim_l

  definition elim_fill'_base {P : Type} {Pb : P} {Pl : Pb = Pb}
    (Pf : Pl = idp) : ap (disc.elim Pb Pl Pf) (fill' circle.base) = idpath Pb :=
  !elim_eq_of_rel

  theorem elim_fill {P : Type} {Pb : P} {Pl : Pb = Pb}
    (Pf : Pl = idp) : square (ap02 (disc.elim Pb Pl Pf) fill) Pf (elim_lp Pf) idp :=
  begin
    esimp [fill,ap02],
    rewrite [+ap_con (ap _),▸*,-ap_compose (ap _) (ap i),+ap_inv],
    xrewrite [eq_top_of_square
               ((ap_compose_natural (disc.elim Pb Pl Pf) i (elim_loop b l))⁻¹ʰ⁻¹ᵛ ⬝h
               (ap_ap_compose (disc.elim Pb Pl Pf) i f loop)⁻¹ʰ⁻¹ᵛ ⬝h
               ap_ap_weakly_constant (disc.elim Pb Pl Pf) fill' loop ⬝h
               ap_con_right_inv_sq (disc.elim Pb Pl Pf) (fill' circle.base)),
               ↑[elim_lp]],
    apply whisker_tl,
    rewrite [ap_weakly_constant_eq,naturality_apdo_eq (λx, !elim_eq_of_rel) loop,▸*,↑elim_2,rec_loop,
            square_of_pathover_concato_eq,square_of_pathover_eq_concato,
            eq_of_square_vconcat_eq,eq_of_square_eq_vconcat],
    -- rewriting here with
    -- rewrite [to_right_inv !pathover_eq_equiv_square (hdeg_square (elim_1 P Pb Pl Pf))],
    -- takes ~11 seconds
    apply eq_vconcat,
    { apply ap (λx, _ ⬝ eq_con_inv_of_con_eq ((_ ⬝ x ⬝ _)⁻¹ ⬝ _) ⬝ _),
      transitivity _, apply ap eq_of_square,
        apply to_right_inv !eq_pathover_equiv_square (hdeg_square (elim_1 P Pb Pl Pf)),
      transitivity _, apply eq_of_square_hdeg_square,
      unfold elim_1, reflexivity},
    rewrite [+con_inv,whisker_left_inv,+inv_inv,-whisker_right_inv,
             con.assoc (whisker_left _ _),con.assoc _ (whisker_right _ _),▸*,
             whisker_right_con_whisker_left _ !ap_constant],
    xrewrite [-con.assoc _ _ (whisker_right _ _)],
    rewrite [con.assoc _ _ (whisker_left _ _),idp_con_whisker_left,▸*,
             con.assoc _ !ap_constant⁻¹,con.left_inv],
    xrewrite [eq_con_inv_of_con_eq_whisker_left,▸*],
    rewrite [+con.assoc _ _ !con.right_inv,right_inv_eq_idp (elim_fill'_base Pf),↑[whisker_left]],
    xrewrite [con2_con_con2],
    rewrite [idp_con,↑elim_fill'_base,con.left_inv,whisker_right_inv,↑whisker_right],
    xrewrite [con.assoc _ _ (_ ◾ _)],
    rewrite [con.left_inv,▸*,-+con.assoc,con.assoc _⁻¹,↑[disc.elim,function.compose],con.left_inv,
             ▸*,↑b,con.left_inv,idp_con],
    apply square_of_eq, reflexivity
  end

  -- protected definition rec_of_elim_sigma {P : disc → Type} (Pb : P base) (Pl : Pb =[lp] Pb)
  --   (Pf : Pl =[fill] idpo) (x : disc) : Σx, P x :=
  -- begin
  -- refine disc.elim _ _ _ x,
  --     { exact ⟨base, Pb⟩},
  --     { exact sigma_eq lp Pl},
  --     { exact sigma_eq2 (!sigma_eq_pr1 ⬝ fill) (!sigma_eq_pr2 ⬝o Pf)}
  -- end

  -- protected definition rec_of_elim {P : disc → Type} (Pb : P base) (Pl : Pb =[lp] Pb)
  --   (Pf : Pl =[fill] idpo) (x : disc) : P x :=
  -- _ ▸ pr2 (disc.rec_of_elim_sigma Pb Pl Pf x)


exit
--  set_option pp.notation false
  protected definition rec {P : disc → Type} (Pb : P base) (Pl : Pb =[lp] Pb)
    (Pf : Pl =[fill] idpo)
    (x : disc) : P x :=
  begin
    induction x,
    { induction a,
      { exact Pb},
      { exact transport P (fill' circle.base) Pb},
      { apply to_inv !(pathover_compose P), exact Pl}},
    { exact abstract begin induction H, induction x,
      { esimp, apply pathover_tr},
      { apply pathover_pathover_fl, apply sorry} end end},
  end
exit
      { esimp, induction x,
        { unfold f, apply pathover_tr},
        { /-apply pathover_pathover_fl,-/ apply sorry}}

  protected definition elim [unfold 5] {P : Type} (Pb : P) (Pl : Pb = Pb)
    (Pf : Pl = idp) (x : disc) : P :=
  begin
    induction x,
    { induction a,
      { exact Pb},
      { exact Pb},
      { exact Pl}},
    { induction H, induction x,
      { exact idpath Pb},
      { exact abstract begin unfold f, apply pathover_eq, apply hdeg_square,
        exact abstract ap_compose (predisc.elim Pb Pb Pl) f loop ⬝
              ap _ !elim_loop ⬝
              !elim_l ⬝
              Pf ⬝
              !ap_constant⁻¹ end end end}},
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
