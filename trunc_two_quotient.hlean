/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn

Declaration of truncated two-quotients
-/

import hit.two_quotient algebra.category.groupoid hit.trunc

open two_quotient eq is_trunc trunc e_closure relation equiv

namespace trunc_two_quotient

  section
  parameters (n : trunc_index) {A : Type}
             (R : A → A → Type)
  local abbreviation T := e_closure R -- the (type-valued) equivalence closure of R
  parameter (Q : Π⦃a a'⦄, T a a' → T a a' → Type)
  variables ⦃a a' a'' : A⦄ {s : R a a'} {t t' : T a a'}

  definition trunc_two_quotient := trunc n (two_quotient R Q)
  definition incl0 (a : A) : trunc_two_quotient := tr (!incl0 a)
  definition incl1 (s : R a a') : incl0 a = incl0 a' := ap tr (!incl1 s)
  definition incltw (t : T a a') : incl0 a = incl0 a' := ap tr (!inclt t)
  definition inclt (t : T a a') : incl0 a = incl0 a' := e_closure.elim incl1 t
  definition incl2w (q : Q t t') : incltw t = incltw t' :=
  ap02 tr (!incl2 q)
  definition incl2 (q : Q t t') : inclt t = inclt t' :=
  !ap_e_closure_elim⁻¹ ⬝ ap02 tr (!incl2 q) ⬝ !ap_e_closure_elim

  parameters {R Q}
  local attribute trunc_two_quotient incl0 [reducible]
  protected definition rec {P : trunc_two_quotient → Type} [H : Πx, is_trunc n (P x)]
    (P0 : Π(a : A), P (incl0 a))
    (P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a =[incl1 s] P0 a')
    (P2 : Π⦃a a' : A⦄ ⦃t t' : T a a'⦄ (q : Q t t'),
      change_path (incl2 q) (e_closure.elimo incl1 P1 t) = e_closure.elimo incl1 P1 t')
    (x : trunc_two_quotient) : P x :=
  begin
    induction x,
    induction a,
    { exact P0 a},
    { exact !pathover_of_pathover_ap (P1 s)},
    { exact sorry}
  end

  protected definition rec_on [reducible] {P : trunc_two_quotient → Type} [H : Πx, is_trunc n (P x)]
    (x : trunc_two_quotient)
    (P0 : Π(a : A), P (incl0 a))
    (P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a =[incl1 s] P0 a')
    (P2 : Π⦃a a' : A⦄ ⦃t t' : T a a'⦄ (q : Q t t'),
      change_path (incl2 q) (e_closure.elimo incl1 P1 t) = e_closure.elimo incl1 P1 t') : P x :=
  rec P0 P1 P2 x

  theorem rec_incl1 {P : trunc_two_quotient → Type} [H : Πx, is_trunc n (P x)]
    (P0 : Π(a : A), P (incl0 a))
    (P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a =[incl1 s] P0 a')
    (P2 : Π⦃a a' : A⦄ ⦃t t' : T a a'⦄ (q : Q t t'),
      change_path (incl2 q) (e_closure.elimo incl1 P1 t) = e_closure.elimo incl1 P1 t')
    ⦃a a' : A⦄ (s : R a a') : apd (rec P0 P1 P2) (incl1 s) = P1 s :=
  !apd_ap ⬝ ap !pathover_ap !rec_incl1 ⬝ to_right_inv !pathover_compose (P1 s)

  theorem rec_inclt {P : trunc_two_quotient → Type} [H : Πx, is_trunc n (P x)]
    (P0 : Π(a : A), P (incl0 a))
    (P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a =[incl1 s] P0 a')
    (P2 : Π⦃a a' : A⦄ ⦃t t' : T a a'⦄ (q : Q t t'),
      change_path (incl2 q) (e_closure.elimo incl1 P1 t) = e_closure.elimo incl1 P1 t')
    ⦃a a' : A⦄ (t : T a a') : apd (rec P0 P1 P2) (inclt t) = e_closure.elimo incl1 P1 t :=
  sorry

  protected definition elim {P : Type} (P0 : A → P) [H : is_trunc n P]
    (P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a')
    (P2 : Π⦃a a' : A⦄ ⦃t t' : T a a'⦄ (q : Q t t'), e_closure.elim P1 t = e_closure.elim P1 t')
    (x : trunc_two_quotient) : P :=
  begin
    induction x,
    induction a,
    { exact P0 a},
    { exact P1 s},
    { exact P2 q},
  end
  local attribute elim [unfold 10]

  protected definition elim_on {P : Type} [H : is_trunc n P] (x : trunc_two_quotient) (P0 : A → P)
    (P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a')
    (P2 : Π⦃a a' : A⦄ ⦃t t' : T a a'⦄ (q : Q t t'), e_closure.elim P1 t = e_closure.elim P1 t')
     : P :=
  elim P0 P1 P2 x

  definition elim_incl1 {P : Type} [H : is_trunc n P] {P0 : A → P}
    {P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a'}
    (P2 : Π⦃a a' : A⦄ ⦃t t' : T a a'⦄ (q : Q t t'), e_closure.elim P1 t = e_closure.elim P1 t')
    ⦃a a' : A⦄ (s : R a a') : ap (elim P0 P1 P2) (incl1 s) = P1 s :=
  !ap_compose⁻¹ ⬝ !elim_incl1

  definition elim_inclt {P : Type} [H : is_trunc n P] {P0 : A → P}
    {P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a'}
    (P2 : Π⦃a a' : A⦄ ⦃t t' : T a a'⦄ (q : Q t t'), e_closure.elim P1 t = e_closure.elim P1 t')
    ⦃a a' : A⦄ (t : T a a') : ap (elim P0 P1 P2) (inclt t) = e_closure.elim P1 t :=
  ap_e_closure_elim_h incl1 (elim_incl1 P2) t

  open function
  theorem elim_incl2 {P : Type} [H : is_trunc n P] (P0 : A → P)
    (P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a')
    (P2 : Π⦃a a' : A⦄ ⦃t t' : T a a'⦄ (q : Q t t'), e_closure.elim P1 t = e_closure.elim P1 t')
    ⦃a a' : A⦄ ⦃t t' : T a a'⦄ (q : Q t t')
    : square (ap02 (elim P0 P1 P2) (incl2 q)) (P2 q) (elim_inclt P2 t) (elim_inclt P2 t') :=
  begin
    note H := elim_incl2 P0 P1 P2 q,
    --note H3 := aps (@tr n _) H,
    --note H2 := ap_ap_e_closure_elim_h (@tr n _) incl1 (elim_incl1 P2) t
--    unfold [elim,elim_inclt,ap02],
    --rewrite [ap_compose (ap trunc.elim)]
    note Ht' := ap_ap_e_closure_elim tr (elim P0 P1 P2) (two_quotient.incl1 R Q) t',
    note Ht := ap_ap_e_closure_elim tr (elim P0 P1 P2) (two_quotient.incl1 R Q) t,
    note Hn := natural_square (ap_compose (elim P0 P1 P2) tr) (two_quotient.incl2 R Q q),
--    note H4 := eq_bot_of_square (natural_square (ap_compose (elim P0 P1 P2) tr) (two_quotient.incl2 R Q q)),
    note H7 := eq_top_of_square (Ht⁻¹ʰ ⬝h Hn⁻¹ᵛ ⬝h Ht'),
    -- note H5 := eq_top_of_square (natural_square (ap_compose (elim P0 P1 P2) tr) (two_quotient.incl2 R Q q)),
    -- esimp [function.compose] at H4,
    unfold [ap02,incl2], rewrite [+ap_con,ap_inv,-ap_compose (ap _)],
    xrewrite [H7],
    clear [Hn, Ht, Ht', H7],
    esimp, exact sorry
  end
  check natural_square_tr
/-
    xrewrite [eq_top_of_square (natural_square (homotopy.symm (ap_compose ((trunc.elim
                (two_quotient.elim R Q Pe @(groupoid_quotient_R.rec Pp)
                   (groupoid_quotient_Q.rec Pid Pcomp Pinv))))
          (@tr 1 _))) (incl2 R Q (Qrefl a)))],
-/

  -- definition elim_inclt_rel [unfold_full] {P : Type} [H : is_trunc n P] {P0 : A → P}
  --   {P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a'}
  --   (P2 : Π⦃a a' : A⦄ ⦃t t' : T a a'⦄ (q : Q t t'), e_closure.elim P1 t = e_closure.elim P1 t')
  --   ⦃a a' : A⦄ (r : R a a') : elim_inclt P2 [r] = elim_incl1 P2 r :=
  -- idp

  -- definition elim_inclt_inv [unfold_full] {P : Type} {P0 : A → P}
  --   {P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a'}
  --   (P2 : Π⦃a a' : A⦄ ⦃t t' : T a a'⦄ (q : Q t t'), e_closure.elim P1 t = e_closure.elim P1 t')
  --   ⦃a a' : A⦄ (t : T a a')
  --   : elim_inclt P2 t⁻¹ʳ = ap_inv (elim P0 P1 P2) (inclt t) ⬝ (elim_inclt P2 t)⁻² :=
  -- idp

  -- definition elim_inclt_con [unfold_full] {P : Type} {P0 : A → P}
  --   {P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a'}
  --   (P2 : Π⦃a a' : A⦄ ⦃t t' : T a a'⦄ (q : Q t t'), e_closure.elim P1 t = e_closure.elim P1 t')
  --   ⦃a a' a'' : A⦄ (t : T a a') (t': T a' a'')
  --   : elim_inclt P2 (t ⬝r t') =
  --       ap_con (elim P0 P1 P2) (inclt t) (inclt t') ⬝ (elim_inclt P2 t ◾ elim_inclt P2 t') :=
  -- idp

  -- definition inclt_rel [unfold_full] (r : R a a') : inclt [r] = incl1 r := idp
  -- definition inclt_inv [unfold_full] (t : T a a') : inclt t⁻¹ʳ = (inclt t)⁻¹ := idp
  -- definition inclt_con [unfold_full] (t : T a a') (t' : T a' a'')
  --   : inclt (t ⬝r t') = inclt t ⬝ inclt t' := idp
end
end trunc_two_quotient
exit

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
  --   : apd (groupoid_quotient.rec Pb Pl1 Pl2 Pf) loop1 = Pl1 :=
  -- sorry

  -- definition rec_loop2 {P : groupoid_quotient → Type} (Pb : P base) (Pl1 : Pb =[loop1] Pb)
  --   (Pl2 : Pb =[loop2] Pb) (Pf : squareover P fill Pl1 Pl1 Pl2 Pl2)
  --   : apd (groupoid_quotient.rec Pb Pl1 Pl2 Pf) loop2 = Pl2 :=
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
  set_option pp.unicode false
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
    esimp [elim_inclt], exact sorry
  end
end
end groupoid_quotient

attribute groupoid_quotient.elt [constructor]
--attribute /-groupoid_quotient.rec-/ groupoid_quotient.elim [unfold 8] [recursor 8]
--attribute groupoid_quotient.elim_type [unfold 9]
--attribute /-groupoid_quotient.rec_on-/ groupoid_quotient.elim_on [unfold 2]
--attribute groupoid_quotient.elim_type_on [unfold 6]
