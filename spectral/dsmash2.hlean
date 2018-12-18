-- Authors: Floris van Doorn

/-

The "dependent" smash product, trying to define it in a different way.

Given A : Type* and B : A → Type* it is the cofiber of
A ∨ B pt → Σ(a : A), B a
We will encode this as a HIT (2-quotient)
-/

import ..pointed_binary hit.two_quotient

open bool pointed eq equiv is_equiv sum bool prod unit circle cofiber sigma.ops wedge sigma
     function prod.ops two_quotient option

namespace dsmash2
  open e_closure
  variables {A : Type*} {B : A → Type*}

  inductive dsmash2_R : option (Σa, B a) → option (Σa, B a) → Type :=
  | Rmk1 : Π(a : A), dsmash2_R (some ⟨a, pt⟩) none
  | Rmk2 : Π(b : B pt), dsmash2_R (some ⟨pt, b⟩) none

  open dsmash2_R
  local abbreviation R := @dsmash2_R

  inductive dsmash2_Q : Π⦃x y : option (Σa, B a)⦄, e_closure R x y → e_closure R x y → Type :=
  | Qmk : dsmash2_Q [Rmk1 pt] [Rmk2 pt]

  open dsmash2_Q
  local abbreviation Q := @dsmash2_Q

  definition dsmash2' (B : A → Type*) : Type := two_quotient R (@Q A B)

  protected definition mk' (a : A) (b : B a) : dsmash2' B := incl0 R Q (some ⟨a, b⟩)

  definition dsmash2 [constructor] (B : A → Type*) : Type* :=
  pointed.MK (dsmash2' B) (dsmash2.mk' pt pt)

  notation `⋀` := dsmash2

  protected definition mk (a : A) (b : B a) : ⋀ B := incl0 R Q (some ⟨a, b⟩)
  definition aux : ⋀ B := incl0 R Q none
  definition gluel (a : A) : dsmash2.mk a pt = aux :> ⋀ B := incl1 R Q (Rmk1 a)
  definition gluer (b : B pt) : dsmash2.mk pt b = aux :> ⋀ B := incl1 R Q (Rmk2 b)
  definition glue2 : gluel pt = gluer pt :> (_ = _ :> ⋀ B) := incl2 R Q Qmk

  definition gluel' (a a' : A) : dsmash2.mk a pt = dsmash2.mk a' pt :> ⋀ B :=
  gluel a ⬝ (gluel a')⁻¹
  definition gluer' (b b' : B pt) : dsmash2.mk pt b = dsmash2.mk pt b' :> ⋀ B :=
  gluer b ⬝ (gluer b')⁻¹
  definition glue (a : A) (b : B pt) : dsmash2.mk a pt = dsmash2.mk pt b :> ⋀ B :=
  gluel a ⬝ (gluer b)⁻¹

  definition glue_pt_left (b : B pt) : glue (Point A) b = gluer' pt b :=
  whisker_right _ glue2

  definition glue_pt_right (a : A) : glue a (Point (B a)) = gluel' a pt :=
  whisker_left _ glue2⁻¹⁻²

  definition ap_mk_left {a a' : A} (p : a = a') : ap (λa, dsmash2.mk a (Point (B a))) p = gluel' a a' :=
  !ap_is_constant

  definition ap_mk_right {b b' : B pt} (p : b = b') : ap (dsmash2.mk (Point A)) p = gluer' b b' :=
  !ap_is_constant

  protected definition rec {P : ⋀ B → Type} (Pmk : Πa b, P (dsmash2.mk a b))
    (Paux : P aux) (Pgl : Πa, Pmk a pt =[gluel a] Paux)
    (Pgr : Πb, Pmk pt b =[gluer b] Paux) (Pg2 : change_path glue2 (Pgl pt) = Pgr pt)
    (x : dsmash2' B) : P x :=
  begin
    induction x with x x x' r x x' r r' q,
    { induction x with x, exact Paux, induction x with a b, exact Pmk a b },
    { induction r,
      { apply Pgl },
      { apply Pgr }},
    { induction q, exact Pg2 }
  end

  theorem rec_gluel {P : ⋀ B → Type} {Pmk : Πa b, P (dsmash2.mk a b)}
    {Paux : P aux} {Pgl : Πa, Pmk a pt =[gluel a] Paux}
    {Pgr : Πb, Pmk pt b =[gluer b] Paux} (Pg2 : change_path glue2 (Pgl pt) = Pgr pt) (a : A) :
    apd (dsmash2.rec Pmk Paux Pgl Pgr Pg2) (gluel a) = Pgl a :=
  !two_quotient.rec_incl1

  theorem rec_gluer {P : ⋀ B → Type} {Pmk : Πa b, P (dsmash2.mk a b)}
    {Paux : P aux} {Pgl : Πa, Pmk a pt =[gluel a] Paux}
    {Pgr : Πb, Pmk pt b =[gluer b] Paux} (Pg2 : change_path glue2 (Pgl pt) = Pgr pt) (b : B pt) :
    apd (dsmash2.rec Pmk Paux Pgl Pgr Pg2) (gluer b) = Pgr b :=
  !two_quotient.rec_incl1

  -- theorem rec_glue {P : ⋀ B → Type} {Pmk : Πa b, P (dsmash2.mk a b)}
  --   {Paux : P aux} {Pgl : Πa, Pmk a pt =[gluel a] Paux}
  --   {Pgr : Πb, Pmk pt b =[gluer b] Paux} (Pg2 : change_path glue2 (Pgl pt) = Pgr pt)
  --   (a : A) (b : B pt) :
  --   apd (dsmash2.rec Pmk Paux Pgl Pgr Pg2) (dsmash2.glue a b) =
  --     (Pgl a ⬝o (Pgl pt)⁻¹ᵒ) ⬝o (Pgr pt ⬝o (Pgr b)⁻¹ᵒ) :=
  -- by rewrite [↑glue, ↑gluel', ↑gluer', +apd_con, +apd_inv, +rec_gluel, +rec_gluer]

  protected definition elim {P : Type} (Pmk : Πa b, P) (Paux : P)
    (Pgl : Πa : A, Pmk a pt = Paux) (Pgr : Πb : B pt, Pmk pt b = Paux) (Pg2 : Pgl pt = Pgr pt)
    (x : dsmash2' B) : P :=
  begin
    induction x with x x x' r x x' r r' q,
    { induction x with x, exact Paux, induction x with a b, exact Pmk a b },
    { induction r,
      { apply Pgl },
      { apply Pgr }},
    { induction q, exact Pg2 }
  end

  definition elim_gluel {P : Type} {Pmk : Πa b, P} {Paux : P}
    {Pgl : Πa : A, Pmk a pt = Paux} {Pgr : Πb : B pt, Pmk pt b = Paux} (Pg2 : Pgl pt = Pgr pt)
    (a : A) : ap (dsmash2.elim Pmk Paux Pgl Pgr Pg2) (gluel a) = Pgl a :=
  proof two_quotient.elim_incl1 _ (Rmk1 a) qed

  definition elim_gluer {P : Type} {Pmk : Πa b, P} {Paux : P}
    {Pgl : Πa : A, Pmk a pt = Paux} {Pgr : Πb : B pt, Pmk pt b = Paux} (Pg2 : Pgl pt = Pgr pt)
    (b : B pt) :
    ap (dsmash2.elim Pmk Paux Pgl Pgr Pg2) (gluer b) = Pgr b :=
  proof !two_quotient.elim_incl1 qed

  theorem elim_glue2 {P : Type} {Pmk : Πa b, P} {Paux : P}
    {Pgl : Πa : A, Pmk a pt = Paux} {Pgr : Πb : B pt, Pmk pt b = Paux} (Pg2 : Pgl pt = Pgr pt) :
    square (ap02 (dsmash2.elim Pmk Paux Pgl Pgr Pg2) glue2) Pg2
           (elim_gluel Pg2 pt) (elim_gluer Pg2 pt) :=
  !two_quotient.elim_incl2

end dsmash2
open dsmash2
attribute dsmash2.mk dsmash2.mk' dsmash2.aux [constructor]
attribute dsmash2.rec dsmash2.elim [unfold 9] [recursor 9]

namespace dsmash2
  variables {A : Type*} {B : A → Type*}


  definition dsmash2_arrow_equiv [constructor] (B : A → Type*) (C : Type) :
    (⋀ B → C) ≃ Σ(f : Πa, B a → C) (c₀ : C) (p : Πa, f a pt = c₀) (q : Πb, f pt b = c₀), p pt = q pt :=
  begin
    fapply equiv.MK,
    { intro f, exact ⟨λa b, f (dsmash2.mk a b), f aux, λa,
                      ap f (gluel a), λb, ap f (gluer b), ap02 f glue2⟩ },
    { intro x, exact dsmash2.elim x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 },
    { intro x, induction x with f x, induction x with c₀ x, induction x with p₁ x, induction x with p₂ q,
      -- apply ap (dpair _), apply ap (dpair _),
      -- refine dpair_eq_dpair (eq_of_homotopy (elim_gluel _)) _,
      -- fapply sigma_pathover,
      -- exact pathover_of_eq _ (eq_of_homotopy (elim_gluer _)),
exact sorry

-- ap02 (dsmash2.elim f c₀ p₁ p₂ q) glue2 =[
--   sigma_eq (eq_of_homotopy (elim_gluel q)) (pathover_of_eq _ (eq_of_homotopy (elim_gluer q)));
--   λ(x : Σ(p : Πa, f a pt = c₀), Πb, f pt b = c₀), x.1 pt = x.2 pt]
-- q

      },
    { intro f, apply eq_of_homotopy, intro x, induction x, reflexivity, reflexivity,
      apply eq_pathover, apply hdeg_square, apply elim_gluel,
      apply eq_pathover, apply hdeg_square, apply elim_gluer,
      exact sorry }
  end

end dsmash2
