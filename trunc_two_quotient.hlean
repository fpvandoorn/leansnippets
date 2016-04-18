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
  parameters (n : ℕ₋₂) {A : Type}
             (R : A → A → Type)
  local abbreviation T := e_closure R -- the (type-valued) equivalence closure of R
  parameter (Q : Π⦃a a'⦄, T a a' → T a a' → Type)
  variables ⦃a a' a'' : A⦄ {s : R a a'} {t t' : T a a'}

  definition trunc_two_quotient := trunc n (two_quotient R Q)

  parameters {n R Q}
  definition incl0 (a : A) : trunc_two_quotient := tr (!incl0 a)
  definition incl1 (s : R a a') : incl0 a = incl0 a' := ap tr (!incl1 s)
  definition incltw (t : T a a') : incl0 a = incl0 a' := ap tr (!inclt t)
  definition inclt (t : T a a') : incl0 a = incl0 a' := e_closure.elim incl1 t
  definition incl2w (q : Q t t') : incltw t = incltw t' :=
  ap02 tr (!incl2 q)
  definition incl2 (q : Q t t') : inclt t = inclt t' :=
  !ap_e_closure_elim⁻¹ ⬝ ap02 tr (!incl2 q) ⬝ !ap_e_closure_elim

  local attribute trunc_two_quotient incl0 [reducible]
  definition is_trunc_trunc_two_quotient [instance] : is_trunc n trunc_two_quotient := _

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
    { exact abstract [irreducible]
      by rewrite [+ e_closure_elimo_ap, ↓incl1, -P2 q, change_path_pathover_of_pathover_ap,
                  - + change_path_con, ↑incl2, con_inv_cancel_right] end}
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

  -- theorem rec_inclt {P : trunc_two_quotient → Type} [H : Πx, is_trunc n (P x)]
  --   (P0 : Π(a : A), P (incl0 a))
  --   (P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a =[incl1 s] P0 a')
  --   (P2 : Π⦃a a' : A⦄ ⦃t t' : T a a'⦄ (q : Q t t'),
  --     change_path (incl2 q) (e_closure.elimo incl1 P1 t) = e_closure.elimo incl1 P1 t')
  --   ⦃a a' : A⦄ (t : T a a') : apd (rec P0 P1 P2) (inclt t) = e_closure.elimo incl1 P1 t :=
  -- sorry

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

  -- MOVE
  definition con.assoc5 {A : Type} {a₁ a₂ a₃ a₄ a₅ a₆ : A}
    (p₁ : a₁ = a₂) (p₂ : a₂ = a₃) (p₃ : a₃ = a₄) (p₄ : a₄ = a₅) (p₅ : a₅ = a₆) :
    p₁ ⬝ (p₂ ⬝ p₃ ⬝ p₄) ⬝ p₅ = (p₁ ⬝ p₂) ⬝ p₃ ⬝ (p₄ ⬝ p₅) :=
  by induction p₅; induction p₄; induction p₃; reflexivity

  theorem elim_incl2 {P : Type} [H : is_trunc n P] (P0 : A → P)
    (P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a')
    (P2 : Π⦃a a' : A⦄ ⦃t t' : T a a'⦄ (q : Q t t'), e_closure.elim P1 t = e_closure.elim P1 t')
    ⦃a a' : A⦄ ⦃t t' : T a a'⦄ (q : Q t t')
    : square (ap02 (elim P0 P1 P2) (incl2 q)) (P2 q) (elim_inclt P2 t) (elim_inclt P2 t') :=
  begin
    note Ht' := ap_ap_e_closure_elim tr (elim P0 P1 P2) (two_quotient.incl1 R Q) t',
    note Ht := ap_ap_e_closure_elim tr (elim P0 P1 P2) (two_quotient.incl1 R Q) t,
    note Hn := natural_square (ap_compose (elim P0 P1 P2) tr) (two_quotient.incl2 R Q q),
    note H7 := eq_top_of_square (Ht⁻¹ʰ ⬝h Hn⁻¹ᵛ ⬝h Ht'), clear [Hn, Ht, Ht'],
    unfold [ap02,incl2], rewrite [+ap_con,ap_inv,-ap_compose (ap _)],
    xrewrite [H7, ↑function.compose, eq_top_of_square (elim_incl2 P0 P1 P2 q)], clear [H7],
    have H : Π(t : T a a'),
      ap_e_closure_elim (elim P0 P1 P2) (λa a' (r : R a a'), ap tr (two_quotient.incl1 R Q r)) t ⬝
      (ap_e_closure_elim_h (two_quotient.incl1 R Q)
        (λa a' (s : R a a'), ap_compose (elim P0 P1 P2) tr (two_quotient.incl1 R Q s)) t)⁻¹ ⬝
      two_quotient.elim_inclt P2 t = elim_inclt P2 t,
    begin
      clear q t t', intro t,
      induction t with a a' r a a' pp a a' r IH a a' a'' r r' IH₁ IH₂,
      { esimp, rewrite idp_con},
      { induction pp, reflexivity},
      { },
      { }
    end,
    rewrite [con.assoc5, con.assoc5, H t, -inv_con_inv_right, -con_inv], xrewrite [H t'],
    apply top_deg_square
  end

  definition elim_inclt_rel [unfold_full] {P : Type} [is_trunc n P] {P0 : A → P}
    {P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a'}
    (P2 : Π⦃a a' : A⦄ ⦃t t' : T a a'⦄ (q : Q t t'), e_closure.elim P1 t = e_closure.elim P1 t')
    ⦃a a' : A⦄ (r : R a a') : elim_inclt P2 [r] = elim_incl1 P2 r :=
  idp

  definition elim_inclt_inv [unfold_full] {P : Type} [is_trunc n P] {P0 : A → P}
    {P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a'}
    (P2 : Π⦃a a' : A⦄ ⦃t t' : T a a'⦄ (q : Q t t'), e_closure.elim P1 t = e_closure.elim P1 t')
    ⦃a a' : A⦄ (t : T a a')
    : elim_inclt P2 t⁻¹ʳ = ap_inv (elim P0 P1 P2) (inclt t) ⬝ (elim_inclt P2 t)⁻² :=
  idp

  definition elim_inclt_con [unfold_full] {P : Type} [is_trunc n P] {P0 : A → P}
    {P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a'}
    (P2 : Π⦃a a' : A⦄ ⦃t t' : T a a'⦄ (q : Q t t'), e_closure.elim P1 t = e_closure.elim P1 t')
    ⦃a a' a'' : A⦄ (t : T a a') (t': T a' a'')
    : elim_inclt P2 (t ⬝r t') =
        ap_con (elim P0 P1 P2) (inclt t) (inclt t') ⬝ (elim_inclt P2 t ◾ elim_inclt P2 t') :=
  idp

  definition inclt_rel [unfold_full] (r : R a a') : inclt [r] = incl1 r := idp
  definition inclt_inv [unfold_full] (t : T a a') : inclt t⁻¹ʳ = (inclt t)⁻¹ := idp
  definition inclt_con [unfold_full] (t : T a a') (t' : T a' a'')
    : inclt (t ⬝r t') = inclt t ⬝ inclt t' := idp


end
end trunc_two_quotient

attribute trunc_two_quotient.incl0 [constructor]
attribute trunc_two_quotient.rec trunc_two_quotient.elim [unfold 10] [recursor 10]
attribute trunc_two_quotient.rec_on trunc_two_quotient.elim_on [unfold 7]
