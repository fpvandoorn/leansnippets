/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn
-/

import hit.circle

open quotient eq circle sum sigma equiv function

section
variables {A B C : Type} {f : A → B} {a a' a₁ a₂ a₃ a₄ : A} {b b' : B}

-- move to square

  definition top_deg_square (p : a₁ = a₂) (q : a₂ = a₃) (r : a₄ = a₃) : square (p ⬝ q ⬝ r⁻¹) q p r :=
  by induction r;induction q;induction p;constructor

  definition square_inv2 {p₁ p₂ p₃ p₄ : a = a'}
    {t : p₁ = p₂} {b : p₃ = p₄} {l : p₁ = p₃} {r : p₂ = p₄} (s : square t b l r)
    : square (inverse2 t) (inverse2 b) (inverse2 l) (inverse2 r) :=
  by induction s;constructor

  definition square_con2 {p₁ p₂ p₃ p₄ : a₁ = a₂} {q₁ q₂ q₃ q₄ : a₂ = a₃}
    {t₁ : p₁ = p₂} {b₁ : p₃ = p₄} {l₁ : p₁ = p₃} {r₁ : p₂ = p₄}
    {t₂ : q₁ = q₂} {b₂ : q₃ = q₄} {l₂ : q₁ = q₃} {r₂ : q₂ = q₄}
    (s₁ : square t₁ b₁ l₁ r₁) (s₂ : square t₂ b₂ l₂ r₂)
      : square (t₁ ◾ t₂) (b₁ ◾ b₂) (l₁ ◾ l₂) (r₁ ◾ r₂) :=
  by induction s₂;induction s₁;constructor

-- move to types.eq

  definition ap_weakly_constant [unfold 8] {A B : Type} {f : A → B} {b : B} (p : Πx, f x = b)
    {x y : A} (q : x = y) : ap f q = p x ⬝ (p y)⁻¹ :=
  by induction q;exact !con.right_inv⁻¹

  theorem ap_weakly_constant_eq {A B : Type} {f : A → B} {b : B} (p : Πx, f x = b)
    {x y : A} (q : x = y) :
      ap_weakly_constant p q =
      eq_con_inv_of_con_eq ((eq_of_square (square_of_pathover (apdo p q)))⁻¹ ⬝
      whisker_left (p x) (ap_constant q b)) :=
  begin
    induction q, esimp, generalize (p x), intro p, cases p, apply idpath idp
  end

  definition inv2_inv {p q : a = a'} (r : p = q) : inverse2 r⁻¹ = (inverse2 r)⁻¹ :=
  by induction r;reflexivity

  definition inv2_con {p p' p'' : a = a'} (r : p = p') (r' : p' = p'')
    : inverse2 (r ⬝ r') = inverse2 r ⬝ inverse2 r' :=
  by induction r';induction r;reflexivity

  definition con2_inv {p₁ q₁ : a₁ = a₂} {p₂ q₂ : a₂ = a₃} (r₁ : p₁ = q₁) (r₂ : p₂ = q₂)
    : (r₁ ◾ r₂)⁻¹ = r₁⁻¹ ◾ r₂⁻¹ :=
  by induction r₁;induction r₂;reflexivity

  theorem eq_con_inv_of_con_eq_whisker_left {A : Type} {a a2 a3 : A}
    {p : a = a2} {q q' : a2 = a3} {r : a = a3} (s' : q = q') (s : p ⬝ q' = r) :
    eq_con_inv_of_con_eq (whisker_left p s' ⬝ s)
      = eq_con_inv_of_con_eq s ⬝ whisker_left r (inverse2 s')⁻¹ :=
  by induction s';induction q;induction s;reflexivity

  theorem right_inv_eq_idp {A : Type} {a : A} {p : a = a} (r : p = idpath a) :
    con.right_inv p = r ◾ inverse2 r :=
  by cases r;reflexivity



-- move to a new file which both imports types.eq and types.cubical.square?

  definition ap_inv2 {p q : a = a'} (r : p = q)
    : square (ap (ap f) (inverse2 r))
             (inverse2 (ap (ap f) r))
             (ap_inv f p)
             (ap_inv f q) :=
  by induction r;exact hrfl

  definition ap_con2 {p₁ q₁ : a₁ = a₂} {p₂ q₂ : a₂ = a₃} (r₁ : p₁ = q₁) (r₂ : p₂ = q₂)
    : square (ap (ap f) (r₁ ◾ r₂))
             (ap (ap f) r₁ ◾ ap (ap f) r₂)
             (ap_con f p₁ p₂)
             (ap_con f q₁ q₂) :=
  by induction r₂;induction r₁;exact hrfl

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

  theorem ap_ap_weakly_constant {A B C : Type} (g : B → C) {f : A → B} {b : B}
    (p : Πx, f x = b) {x y : A} (q : x = y) :
    square (ap (ap g) (ap_weakly_constant p q))
           (ap_weakly_constant (λa, ap g (p a)) q)
           (ap_compose g f q)⁻¹
           (!ap_con ⬝ whisker_left _ !ap_inv) :=
  begin
    induction q, esimp, generalize (p x), intro p, cases p, apply ids
--    induction q, rewrite [↑ap_compose,ap_inv], apply hinverse, apply ap_con_right_inv_sq,
  end

  theorem ap_ap_compose {A B C D : Type} (h : C → D) (g : B → C) (f : A → B)
    {x y : A} (p : x = y) :
    square (ap_compose (h ∘ g) f p)
           (ap (ap h) (ap_compose g f p))
           (ap_compose h (g ∘ f) p)
           (ap_compose h g (ap f p)) :=
  by induction p;exact ids

  theorem ap_compose_inv {A B C : Type} (g : B → C) (f : A → B)
    {x y : A} (p : x = y) :
    square (ap_compose g f p⁻¹)
           (inverse2 (ap_compose g f p) ⬝ (ap_inv g (ap f p))⁻¹)
           (ap_inv (g ∘ f) p)
           (ap (ap g) (ap_inv f p)) :=
  by induction p;exact ids

  theorem ap_compose_con (g : B → C) (f : A → B) (p : a₁ = a₂) (q : a₂ = a₃) :
    square (ap_compose g f (p ⬝ q))
           (ap_compose g f p ◾ ap_compose g f q ⬝ (ap_con g (ap f p) (ap f q))⁻¹)
           (ap_con (g ∘ f) p q)
           (ap (ap g) (ap_con f p q)) :=
  by induction q;induction p;exact ids

  theorem ap_compose_natural {A B C : Type} (g : B → C) (f : A → B)
    {x y : A} {p q : x = y} (r : p = q) :
    square (ap (ap (g ∘ f)) r)
           (ap (ap g ∘ ap f) r)
           (ap_compose g f p)
           (ap_compose g f q) :=
  natural_square (ap_compose g f) r

-- definition naturality_apdo {A : Type} {B : A → Type} {a a₂ : A} {f g : Πa, B a}
--   (H : f ~ g) (p : a = a₂)
--   : squareover B vrfl (apdo f p) (apdo g p)
--                       (pathover_idp_of_eq (H a)) (pathover_idp_of_eq (H a₂)) :=
-- by induction p;esimp;exact hrflo

definition naturality_apdo_eq {A : Type} {B : A → Type} {a a₂ : A} {f g : Πa, B a}
  (H : f ~ g) (p : a = a₂)
  : apdo f p = concato_eq (eq_concato (H a) (apdo g p)) (H a₂)⁻¹ :=
begin
  induction p, esimp,
  generalizes [H a, g a], intro ga Ha, induction Ha,
  reflexivity
end

end



namespace two_quotient_ext

  section
  parameters {A : Type}
             (R : A → A → Type)

  -- symmetric transitive closure
  inductive st_closure : A → A → Type :=
  | of_rel : Π{a a'} (r : R a a'), st_closure a a'
  | symm : Π{a a'} (r : st_closure a a'), st_closure a' a
  | trans : Π{a a' a''} (r : st_closure a a') (r' : st_closure a' a''), st_closure a a''
  open st_closure
  local abbreviation T := st_closure
  variables ⦃a a' : A⦄ {s : R a a'} {r : T a a}

  protected definition st_closure.elim {B : Type} {f : A → B}
    (e : Π⦃a a' : A⦄, R a a' → f a = f a') (t : T a a') : f a = f a' :=
  begin
    induction t,
      exact e r,
      exact v_0⁻¹,
      exact v_0 ⬝ v_1
  end

  definition ap_st_closure_elim_h {B C : Type} {f : A → B} {g : B → C}
    (e : Π⦃a a' : A⦄, R a a' → f a = f a')
    {e' : Π⦃a a' : A⦄, R a a' → g (f a) = g (f a')}
    (p : Π⦃a a' : A⦄ (s : R a a'), ap g (e s) = e' s) (t : T a a')
    : ap g (st_closure.elim e t) = st_closure.elim e' t :=
  begin
    induction t,
      apply p,
      exact ap_inv g (st_closure.elim e r) ⬝ inverse2 v_0,
      exact ap_con g (st_closure.elim e r) (st_closure.elim e r') ⬝ (v_0 ◾ v_1)
  end

  definition ap_st_closure_elim {B C : Type} {f : A → B} (g : B → C)
    (e : Π⦃a a' : A⦄, R a a' → f a = f a') (t : T a a')
    : ap g (st_closure.elim e t) = st_closure.elim (λa a' r, ap g (e r)) t :=
  ap_st_closure_elim_h e (λa a' s, idp) t

  theorem ap_ap_st_closure_elim_h {B C D : Type} {f : A → B}
    {g : B → C} (h : C → D)
    (e : Π⦃a a' : A⦄, R a a' → f a = f a')
    {e' : Π⦃a a' : A⦄, R a a' → g (f a) = g (f a')}
    (p : Π⦃a a' : A⦄ (s : R a a'), ap g (e s) = e' s) (t : T a a')
    : square (ap (ap h) (ap_st_closure_elim_h e p t))
             (ap_st_closure_elim_h e (λa a' s, ap_compose h g (e s)) t)
             (ap_compose h g (st_closure.elim e t))⁻¹
             (ap_st_closure_elim_h e' (λa a' s, (ap (ap h) (p s))⁻¹) t) :=
  begin
    induction t,
    { unfold [ap_st_closure_elim_h,st_closure.elim],
      apply square_of_eq, exact !con.right_inv ⬝ !con.left_inv⁻¹},
    { rewrite [↑st_closure.elim,
               ↑ap_st_closure_elim_h,
               ap_con (ap h)],
      refine (transpose !ap_compose_inv)⁻¹ᵛ ⬝h _,
      rewrite [con_inv,inv_inv,-inv2_inv],
      exact !ap_inv2 ⬝v square_inv2 v_0},
    { rewrite [↑st_closure.elim,
               ↑ap_st_closure_elim_h,
               ap_con (ap h)],
      refine (transpose !ap_compose_con)⁻¹ᵛ ⬝h _,
      rewrite [con_inv,inv_inv,con2_inv],
      refine !ap_con2 ⬝v square_con2 v_0 v_1},
  end

  theorem ap_ap_st_closure_elim {B C D : Type} {f : A → B}
    (g : B → C) (h : C → D)
    (e : Π⦃a a' : A⦄, R a a' → f a = f a') (t : T a a')
    : square (ap (ap h) (ap_st_closure_elim g e t))
             (ap_st_closure_elim_h e (λa a' s, ap_compose h g (e s)) t)
             (ap_compose h g (st_closure.elim e t))⁻¹
             (ap_st_closure_elim h (λa a' r, ap g (e r)) t) :=
  !ap_ap_st_closure_elim_h

  -- definition ap_ap_st_closure_elim {B C D : Type} {f : A → B} {g : B → C} (h : C → D)
  --   (e : Π⦃a a' : A⦄, R a a' → f a = f a') (t : T a a')
  --   : square (ap (ap h) (ap_st_closure_elim g e t))
  --            (ap_st_closure_elim (h ∘ g) e t)
  --            (ap_compose h g (st_closure.elim e t))⁻¹
  --            (ap_st_closure_elim_h (λa a' s, (ap_compose h g (e s))⁻¹) t) :=
  -- begin
  --   induction t,
  -- end


  parameter (Q : Π⦃a⦄, T a a → Type)


  local abbreviation B := A ⊎ Σ(a : A) (r : T a a), Q r

  inductive pre_two_quotient_ext_rel : B → B → Type :=
  | pre_Rmk {} : Π⦃a a'⦄ (r : R a a'), pre_two_quotient_ext_rel (inl a) (inl a')
  --BUG: if {} not provided, the alias for pre_Rmk is wrong

  definition pre_two_quotient_ext := quotient pre_two_quotient_ext_rel

  open pre_two_quotient_ext_rel
  local abbreviation C := quotient pre_two_quotient_ext_rel
  protected definition j [constructor] (a : A) : C := class_of pre_two_quotient_ext_rel (inl a)
  protected definition pre_aux [constructor] (q : Q r) : C :=
  class_of pre_two_quotient_ext_rel (inr ⟨a, r, q⟩)
  protected definition e (s : R a a') : j a = j a' := eq_of_rel _ (pre_Rmk s)
  protected definition et (t : T a a') : j a = j a' := st_closure.elim e t
  protected definition f [unfold 7] (q : Q r) : S¹ → C :=
  circle.elim (j a) (et r)

  protected definition pre_rec [unfold 8] {P : C → Type}
    (Pj : Πa, P (j a)) (Pa : Π⦃a : A⦄ ⦃r : T a a⦄ (q : Q r), P (pre_aux q))
    (Pe : Π⦃a a' : A⦄ (s : R a a'), Pj a =[e s] Pj a') (x : C) : P x :=
  begin
    induction x with p,
    { induction p,
      { apply Pj},
      { induction a with a1 a2, induction a2, apply Pa}},
    { induction H, esimp, apply Pe},
  end

  protected definition pre_elim [unfold 8] {P : Type} (Pj : A → P)
    (Pa : Π⦃a : A⦄ ⦃r : T a a⦄, Q r → P) (Pe : Π⦃a a' : A⦄ (s : R a a'), Pj a = Pj a') (x : C)
    : P :=
  pre_rec Pj Pa (λa a' s, pathover_of_eq (Pe s)) x

  protected theorem rec_e {P : C → Type}
    (Pj : Πa, P (j a)) (Pa : Π⦃a : A⦄ ⦃r : T a a⦄ (q : Q r), P (pre_aux q))
    (Pe : Π⦃a a' : A⦄ (s : R a a'), Pj a =[e s] Pj a') ⦃a a' : A⦄ (s : R a a')
    : apdo (pre_rec Pj Pa Pe) (e s) = Pe s :=
  !rec_eq_of_rel

  protected theorem elim_e {P : Type} (Pj : A → P) (Pa : Π⦃a : A⦄ ⦃r : T a a⦄, Q r → P)
    (Pe : Π⦃a a' : A⦄ (s : R a a'), Pj a = Pj a') ⦃a a' : A⦄ (s : R a a')
    : ap (pre_elim Pj Pa Pe) (e s) = Pe s :=
  begin
    apply eq_of_fn_eq_fn_inv !(pathover_constant (e s)),
    rewrite [▸*,-apdo_eq_pathover_of_eq_ap,↑pre_elim,rec_e],
  end

  protected theorem elim_et {P : Type} (Pj : A → P) (Pa : Π⦃a : A⦄ ⦃r : T a a⦄, Q r → P)
    (Pe : Π⦃a a' : A⦄ (s : R a a'), Pj a = Pj a') ⦃a a' : A⦄ (t : T a a')
    : ap (pre_elim Pj Pa Pe) (et t) = st_closure.elim Pe t :=
  ap_st_closure_elim_h e (elim_e Pj Pa Pe) t

  inductive two_quotient_ext_rel : C → C → Type :=
  | Rmk {} : Π{a : A} {r : T a a} (q : Q r) (x : circle), two_quotient_ext_rel (f q x) (pre_aux q)

  open two_quotient_ext_rel
  definition two_quotient_ext := quotient two_quotient_ext_rel
  local abbreviation D := two_quotient_ext
  local abbreviation i := class_of two_quotient_ext_rel
  definition incl0 (a : A) : D := i (j a)
  definition aux (q : Q r) : D := i (pre_aux q)
  definition incl1 (s : R a a') : incl0 a = incl0 a' := ap i (e s)
--  definition inclt_wrong (t : T a a') : incl0 a = incl0 a' := ap i (et t)
  definition inclt (t : T a a') : incl0 a = incl0 a' := st_closure.elim incl1 t
  definition inclt_eq_ap (t : T a a') : inclt t = ap i (et t) :=
  (ap_st_closure_elim i e t)⁻¹

  definition incl2' (q : Q r) (x : S¹) : i (f q x) = aux q :=
  eq_of_rel two_quotient_ext_rel (Rmk q x)

  definition incl2 (q : Q r) : inclt r = idp :=
  inclt_eq_ap r ⬝
  (ap02 i (elim_loop (j a) (et r))⁻¹) ⬝
  (ap_compose i (f q) loop)⁻¹ ⬝
  ap_weakly_constant (incl2' q) loop ⬝
  !con.right_inv

  local attribute two_quotient_ext f i incl0 aux incl1 incl2' inclt [reducible]
  local attribute i aux incl0 [constructor]
  --TO CONSIDER: should all definitions about pre-structure be reducible?
  protected definition elim {P : Type} (P0 : A → P)
    (P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a')
    (P2 : Π⦃a : A⦄ ⦃r : T a a⦄ (q : Q r), st_closure.elim P1 r = idp)
    (x : D) : P :=
  begin
    induction x,
    { refine (pre_elim _ _ _ a),
      { exact P0},
      { intro a r q, exact P0 a},
      { exact P1}},
    { exact abstract begin induction H, induction x,
      { exact idpath (P0 a)},
      { unfold f, apply eq_pathover, apply hdeg_square,
        exact abstract ap_compose (pre_elim P0 _ P1) (f q) loop ⬝
              ap _ !elim_loop ⬝
              !elim_et ⬝
              P2 q ⬝
              !ap_constant⁻¹ end
} end end},
  end
  local attribute elim [unfold 8]

  protected definition elim_on {P : Type} (x : D) (P0 : A → P)
    (P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a')
    (P2 : Π⦃a : A⦄ ⦃r : T a a⦄ (q : Q r), st_closure.elim P1 r = idp)
     : P :=
  elim P0 P1 P2 x

  definition elim_incl1 {P : Type} {P0 : A → P}
    {P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a'}
    (P2 : Π⦃a : A⦄ ⦃r : T a a⦄ (q : Q r), st_closure.elim P1 r = idp)
    ⦃a a' : A⦄ (s : R a a') : ap (elim P0 P1 P2) (incl1 s) = P1 s :=
  !ap_compose⁻¹ ⬝ !elim_e

  definition elim_inclt {P : Type} {P0 : A → P}
    {P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a'}
    (P2 : Π⦃a : A⦄ ⦃r : T a a⦄ (q : Q r), st_closure.elim P1 r = idp)
    ⦃a a' : A⦄ (t : T a a') : ap (elim P0 P1 P2) (inclt t) = st_closure.elim P1 t :=
  ap_st_closure_elim_h incl1 (elim_incl1 P2) t

  definition elim_incl2'_incl0 {P : Type} {P0 : A → P}
    {P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a'}
    (P2 : Π⦃a : A⦄ ⦃r : T a a⦄ (q : Q r), st_closure.elim P1 r = idp)
    ⦃a : A⦄ ⦃r : T a a⦄ (q : Q r) : ap (elim P0 P1 P2) (incl2' q base) = idpath (P0 a) :=
  !elim_eq_of_rel

  -- theorem ap_ap_st_closure_elim_h {B C D : Type} {f : A → B}
  --   {g : B → C} (h : C → D)
  --   (e : Π⦃a a' : A⦄, R a a' → f a = f a')
  --   {e' : Π⦃a a' : A⦄, R a a' → g (f a) = g (f a')}
  --   (p : Π⦃a a' : A⦄ (s : R a a'), ap g (e s) = e' s) (t : T a a')

exit
  -- set_option pp.implicit true
  theorem elim_incl2 {P : Type} (P0 : A → P)
    (P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a')
    (P2 : Π⦃a : A⦄ ⦃r : T a a⦄ (q : Q r), st_closure.elim P1 r = idp)
    ⦃a : A⦄ ⦃r : T a a⦄ (q : Q r)
    : square (ap02 (elim P0 P1 P2) (incl2 q)) (P2 q) (elim_inclt P2 r) idp :=
  begin
/-
  theorem ap_ap_st_closure_elim {B C D : Type} {f : A → B}
    (g : B → C) (h : C → D)
    (e : Π⦃a a' : A⦄, R a a' → f a = f a') (t : T a a')
    : square (ap (ap h) (ap_st_closure_elim g e t))
             (ap_st_closure_elim_h e (λa a' s, ap_compose h g (e s)) t)
             (ap_compose h g (st_closure.elim e t))⁻¹
             (ap_st_closure_elim h (λa a' r, ap g (e r)) t) :=
  !ap_ap_st_closure_elim_h

-/

    -- assert H : square (ap (ap (elim P0 P1 P2)) (inclt_eq_ap r)⁻¹)
    --          (ap_st_closure_elim_h e (λa a' s, ap_compose (elim P0 P1 P2) i (e s)) r)
    --          (ap_compose (elim P0 P1 P2) i (st_closure.elim e r))⁻¹
    --          (ap_st_closure_elim (elim P0 P1 P2) (λa a' r, ap i (e r)) r)
    --                   ,
    -- { },

    esimp [incl2,ap02],
    rewrite [+ap_con (ap _),▸*], --,-ap_compose (ap _) (ap i),+ap_inv],
    xrewrite [-ap_compose (ap _) (ap i)],
    rewrite [↑inclt_eq_ap,+ap_inv],
    xrewrite [eq_top_of_square
               ((ap_ap_st_closure_elim i (elim P0 P1 P2) e r)⁻¹ʰ ⬝h
               (ap_compose_natural (elim P0 P1 P2) i (elim_loop (j a) (et r)))⁻¹ʰ⁻¹ᵛ ⬝h
               (ap_ap_compose (elim P0 P1 P2) i (f q) loop)⁻¹ʰ⁻¹ᵛ ⬝h
               ap_ap_weakly_constant (elim P0 P1 P2) (incl2' q) loop ⬝h
               ap_con_right_inv_sq (elim P0 P1 P2) (incl2' q base)),
               ↑[elim_inclt]],
    apply whisker_tl,
    rewrite [ap_weakly_constant_eq],
    xrewrite [naturality_apdo_eq (λx, !elim_eq_of_rel) loop],
    rewrite [↑elim_2,rec_loop,square_of_pathover_concato_eq,square_of_pathover_eq_concato,
            eq_of_square_vconcat_eq,eq_of_square_eq_vconcat],
    apply eq_vconcat,
    { apply ap (λx, _ ⬝ eq_con_inv_of_con_eq ((_ ⬝ x ⬝ _)⁻¹ ⬝ _) ⬝ _),
      transitivity _, apply ap eq_of_square,
        apply to_right_inv !pathover_eq_equiv_square (hdeg_square (elim_1 P A R Q P0 P1 a r q P2)),
      transitivity _, apply eq_of_square_hdeg_square,
      unfold elim_1, reflexivity},
end exit
    rewrite [+con_inv,whisker_left_inv,+inv_inv,-whisker_right_inv,
             con.assoc (whisker_left _ _),con.assoc _ (whisker_right _ _),▸*,
             whisker_right_con_whisker_left _ !ap_constant],
    xrewrite [-con.assoc _ _ (whisker_right _ _)],
    rewrite [con.assoc _ _ (whisker_left _ _),idp_con_whisker_left,▸*,
             con.assoc _ !ap_constant⁻¹,con.left_inv],
    xrewrite [eq_con_inv_of_con_eq_whisker_left,▸*],
    rewrite [+con.assoc _ _ !con.right_inv,
             right_inv_eq_idp (
               (λ(x : ap (elim P0 P1 P2) (incl2' q base) = idpath
               (elim P0 P1 P2 (class_of two_quotient_ext_rel (f q base)))), x)
                (elim_incl2'_incl0 P2 q)),
             ↑[whisker_left]],
    xrewrite [con2_con_con2],
    rewrite [idp_con,↑elim_incl2'_incl0,con.left_inv,whisker_right_inv,↑whisker_right],
    xrewrite [con.assoc _ _ (_ ◾ _)],
    rewrite [con.left_inv,▸*,-+con.assoc,con.assoc _⁻¹,↑[elim,function.compose],con.left_inv,
             ▸*,↑j,con.left_inv,idp_con],
    apply square_of_eq, reflexivity
  end

end
namespace st_closure
  infix `⬝r`:75 := st_closure.trans
  postfix `⁻¹ʳ`:(max+10) := st_closure.symm
end st_closure
end two_quotient_ext

--attribute two_quotient_ext.j [constructor] --TODO
attribute /-two_quotient_ext.rec-/ two_quotient_ext.elim [unfold 8] [recursor 8]
--attribute two_quotient_ext.elim_type [unfold 9]
attribute /-two_quotient_ext.rec_on-/ two_quotient_ext.elim_on [unfold 5]
--attribute two_quotient_ext.elim_type_on [unfold 6]
