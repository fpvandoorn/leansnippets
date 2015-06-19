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

  definition ap_eq_idp {A B : Type} {f : A → B} {b : B} (p : Πx, f x = b) {x : A}
    (q : x = x) : ap f q = idp :=
  cancel_right (ap_con_eq p q ⬝ !idp_con⁻¹)

definition eq2_of_circle_eq' {q : b' = b'} (H : Πx, circle.elim b' q x = b) : q = idp :=
!elim_loop⁻¹ ⬝ ap_eq_idp H _

definition eq2_of_circle_eq {q : a' = a'} (H : Πx, f (circle.elim a' q x) = b) : ap f q = idp :=
(ap02 f (elim_loop a' q))⁻¹ ⬝ (ap_compose f (circle.elim a' q) loop)⁻¹ ⬝ ap_eq_idp H loop

definition ap02_eq2_of_circle_eq (g : B → C) {q : a' = a'} (H : Πx, f (circle.elim a' q x) = b)
 : square (eq2_of_circle_eq (λx, (ap g) (H x))) (ap02 g (eq2_of_circle_eq H))
     (ap_compose g f q) idp :=
begin
  exact sorry
end

  theorem ap_con_right_inv_sq {A B : Type} {a1 a2 : A} (f : A → B) (p : a1 = a2) :
    square (ap (ap f) (con.right_inv p))
           (con.right_inv (ap f p))
           (ap_con f p p⁻¹ ⬝ whisker_left _ (ap_inv f p))
           idp :=
  by cases p;apply hrefl

  theorem ap_con_left_inv_sq {A B : Type} {a1 a2 : A} (f : A → B) (p : a1 = a2) :
    square (ap (ap f) (con.left_inv p))
           (con.left_inv (ap f p))
           (ap_con f p⁻¹ p ⬝ whisker_right (ap_inv f p) _)
           idp :=
  by cases p;apply vrefl

  definition ap_weakly_constant [unfold-c 8] {A B : Type} {f : A → B} {b : B} (p : Πx, f x = b)
    {x y : A} (q : x = y) : ap f q = p x ⬝ (p y)⁻¹ :=
  by induction q;exact !con.right_inv⁻¹

  definition ap_ap_weakly_constant {A B C : Type} {g : B → C} {f : A → B} {b : B}
    (p : Πx, f x = b) {x y : A} (q : x = y) :
    square (ap (ap g) (ap_weakly_constant p q))
           (ap_weakly_constant (λa, ap g (p a)) q)
           (ap_compose g f q)⁻¹
           (!ap_con ⬝ whisker_left _ !ap_inv) :=
  begin
    induction q, rewrite [↑ap_compose,ap_inv], apply hinverse, apply ap_con_right_inv_sq,
  end

  definition ap_ap_compose {A B C D : Type} (h : C → D) (g : B → C) (f : A → B)
    {x y : A} (p : x = y) :
    square (ap_compose (h ∘ g) f p)
           (ap (ap h) (ap_compose g f p))
           (ap_compose h (g ∘ f) p)
           (ap_compose h g (ap f p)) :=
  by induction p;exact ids

  definition ap_compose_natural {A B C : Type} (g : B → C) (f : A → B)
    {x y : A} {p q : x = y} (r : p = q) :
    square (ap (ap (g ∘ f)) r)
           (ap (ap g ∘ ap f) r)
           (ap_compose g f p)
           (ap_compose g f q) :=
  natural_square (ap_compose g f) r

--     : ap (ap g) (ap_weakly_constant p q) = (ap_compose g f q)⁻¹ ⬝
--   ap_weakly_constant (λa, ap g (p a)) q ⬝ (!ap_con ⬝ whisker_left _ !ap_inv)⁻¹ :=
--   begin
--     induction q,
--     esimp,
-- --    refine ap inverse (!ap_con_right_inv⁻¹) ⬝ _
--       apply sorry
--   end



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
  definition f [reducible] : S¹ → predisc :=
  circle.elim b l


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
  private definition i : predisc → disc := class_of disc_rel
  definition base : disc := i b
  definition aux  : disc := i e
  definition lp : base = base := ap i l
  definition fill' (x : S¹) : i (f x) = aux := eq_of_rel disc_rel (Rf x)
  definition fill  : lp = idp :=
  (ap02 i (elim_loop b l)⁻¹) ⬝
  (ap_compose i f loop)⁻¹ ⬝
  ap_weakly_constant fill' loop ⬝
  !con.right_inv

  local attribute disc i base aux lp fill' [reducible]

  -- definition fill : lp = idp :=
  -- eq2_of_circle_eq fill'

  -- definition fill2' (x : S¹) : circle.elim base lp x = aux :=
  -- circle.rec_on x (eq_of_rel disc_rel (Rf circle.base)) (pathover_eq begin rewrite [ap_constant,elim_loop], apply square_of_eq, refine !idp_con⁻¹ ⬝ ap (λx, x ⬝ _) _, end )

  -- definition fill2  : lp = idp :=
  -- eq2_of_circle_eq' fill2'

    -- necessary for proofs of fill/fill' in torus:
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
    { induction H, induction x,
      { exact idpath Pb},
      { exact abstract begin unfold f, apply pathover_eq, apply hdeg_square,
        exact ap_compose (predisc.elim Pb Pb Pl) f loop ⬝
              ap _ !elim_loop ⬝
              !elim_l ⬝
              Pf ⬝
              !ap_constant⁻¹ end end}},
  end

  definition elim_lp {P : Type} {Pb : P} {Pl : Pb = Pb}
    (Pf : Pl = idp) : ap (disc.elim Pb Pl Pf) lp = Pl :=
  !ap_compose⁻¹ ⬝ !elim_l

--   definition foo {A B C : Type} (f : A → B) (g : B → C) {x y : A} {p q : x = y} (r : p = q) :
--     ap (g ∘ f) p = ap g (ap f p) :=
--   begin
--     check_expr ap_con_eq_con_ap (ap_compose f g) r, apply sorry
--   end
-- check (class_of disc_rel : predisc → disc)


-- --definition mysorry (A : Type) : A := sorry

--   definition elim_fill'_base {P : Type} {Pb : P} {Pl : Pb = Pb}
--     (Pf : Pl = idp) : ap (disc.elim Pb Pl Pf) (fill' circle.base) = idpath Pb :=
--   begin
--     rewrite [↑disc.elim, ↑fill'],
--     krewrite [elim_eq_of_rel],
--   end

--   definition elim_fill' {P : Type} {Pb : P} {Pl : Pb = Pb}
--     (Pf : Pl = idp) (x : circle) : apd (λx, ap (disc.elim Pb Pl Pf) (fill' x)) loop = sorry :=
--   begin
--     rewrite [↑disc.elim, ↑fill'],
-- --    krewrite [▸*],
--   end

-- check natural_square (ap_compose _ _) _
  --set_option pp.implicit true
  definition elim_fill {P : Type} {Pb : P} {Pl : Pb = Pb}
    (Pf : Pl = idp) : square (ap02 (disc.elim Pb Pl Pf) fill) Pf (elim_lp Pf) idp :=
  begin
    esimp [fill,ap02],
    rewrite [+ap_con (ap _),▸*,-ap_compose (ap (disc.elim Pb Pl Pf)) (ap i) (elim_loop b l)⁻¹, ap_inv (ap _)],
    rewrite [eq_top_of_square ((ap_compose_natural _ _ _)⁻¹ᵛ)],
   xrewrite [eq_top_of_square ((ap_ap_compose (disc.elim Pb Pl Pf) i f loop)⁻¹ʰ⁻¹ᵛ)], --eq_top_of_square ((ap_compose_natural _ _ _)⁻¹ᵛ)
    check_expr (ap_compose_natural (disc.elim Pb Pl Pf) i (elim_loop b l))⁻¹ᵛ ⬝h
     (_)⁻¹ᵛ ⬝h
     (ap_ap_compose (disc.elim Pb Pl Pf) i f loop)⁻¹ʰ⁻¹ᵛ,
    check_expr (ap_compose (disc.elim Pb Pl Pf) i l),
    check_expr (ap_compose (disc.elim Pb Pl Pf) i (ap f loop)),
  end
    -- refine ((ap02_eq2_of_circle_eq (disc.elim Pb Pl Pf) fill')⁻¹ᵛ ⬝v _),
    -- esimp [eq2_of_circle_eq,function.compose,disc.elim,ap02,ap_eq_idp,ap_con_eq,fill'],
    -- check_expr (ap02 (disc.elim Pb Pl Pf ∘ class_of disc_rel) (elim_loop b l))⁻¹,
    -- check_expr (idp : disc.elim Pb Pl Pf ∘ class_of disc_rel = predisc.elim Pb Pb Pl),
    -- assert H : ap (disc.elim Pb Pl Pf) (fill' circle.base) = sorry,
    -- { }
    --rewrite [elim_eq_of_rel],
    --esimp [elim_loop,ap02]
    -- check_expr ap_con_eq_con_ap (ap_compose (disc.elim Pb Pl Pf) (class_of disc_rel)) (elim_loop b l)
    --rewrite [ap_compose]
    --rewrite [elim_eq_of_rel],

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
