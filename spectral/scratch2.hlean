import cohomology.basic
open cohomology algebra int fwedge choice
set_option pp.universes true
set_option pp.abbreviations false
print unreduced_ordinary_cohomology
print is_contr_ordinary_cohomology
print unreduced_ordinary_cohomology_sphere_of_neq
print unreduced_ordinary_cohomology_nonzero
print unreduced_cohomology_split
print cohomology_wedge
print wedge.wedge_pequiv
print cohomology_fwedge
print fwedge.trunc_fwedge_pmap_equiv
print fwedge_pmap_equiv
print choice_equiv
exit

import .pointed_pi
import algebra.product_group

open fiber eq is_trunc is_conn trunc susp equiv is_equiv pointed algebra group nat function sigma sigma.ops

open int prod prod.ops

set_option pp.coercions true
definition add_ab_group_coercion [instance] (A : AddAbGroup) : add_ab_group (algebra._trans_of_Group_of_AbGroup_2 A) :=
AbGroup.struct A



exit
open trunc_index prod fin
universe variable u



  definition ppi_functor [constructor] {A' A : Type*} {B : A → Type} {B' : A' → Type}
    {b : B pt} {b' : B' pt} (f : A' →* A) (g : Πa', B (f a') → B' a')
    (p : g pt (transport B (respect_pt f)⁻¹ b) = b') (h : ppi B b) : ppi B' b' :=
  proof
  ppi.mk (λa', g a' (h (f a')))
             (ap (λx, g pt x) (eq_tr_of_pathover (apd h (respect_pt f) ⬝op respect_pt h)) ⬝ p)
  qed

  definition ppi_functor_left [constructor] {A' A : Type*} {B : A → Type}
    (f : A' →* A) {b : B pt} {b' : B (f pt)} (p : b' =[respect_pt f] b) (g : ppi B b) :
    ppi (B ∘ f) b' :=
  proof ppi_functor f (λa, id) (tr_eq_of_pathover p⁻¹ᵒ) g qed

  -- definition ppi_functor_left_ppi_const [constructor] {A' A : Type*} {B : A → Type}
  --   (f : A' →* A) {b : B pt} {b' : B (f pt)} (p : b' =[respect_pt f] b) : ppi_functor_left_ppi_const _ _ ~* ppi_const (B ∘ f) :=
  -- phomotopy.mk homotopy.rfl proof !eq_tr_of_pathover_con_tr_eq_of_pathover⁻¹ ⬝ whisker_right _ !ap_id⁻¹ qed

  definition respect_pt_ppi_functor_left [constructor] {A' : Type*} {A : Type} {B : A → Type}
    (f : A' → A) {b : B (f pt)} (g : ppi B b) :
    respect_pt (@ppi_functor_left A' (pointed.MK A (f pt)) B (pmap_of_map_pt f) _ _
      idpo g) = respect_pt g :=
  sorry

  definition ppi_compose_pmap [constructor] {A' A : Type*} {B : A → Type*}
    (f : A' →* A) (g : Π*(a : A), B a) :  Π*(a' : A'), B (f a') :=
  ppi_functor_left f (apd (λa, Point (B a)) (respect_pt f)) g

  definition ppi_compose_pmap_ppi_const [constructor] {A' A : Type*} (B : A → Type*)
    (f : A' →* A) : ppi_compose_pmap f (ppi_const B) ~* ppi_const (B ∘ f) :=
  phomotopy.mk homotopy.rfl proof !eq_tr_of_pathover_con_tr_eq_of_pathover⁻¹ ⬝ whisker_right _ !ap_id⁻¹ qed

  definition ppi_compose_right [constructor] {A' A : Type*} (B : A → Type*)
    (f : A' →* A) : (Π*(a : A), B a) →* Π*(a' : A'), B (f a') :=
  pmap.mk (ppi_compose_pmap f) (eq_of_phomotopy (ppi_compose_pmap_ppi_const B f))

  definition ppi_eq_equiv_natural_left_gen_lem {A' A : Type*} {B : A → Type} {f : A' →* A}
    {b₀ : B pt} {b₀' : B (f pt)} {k l : ppi B b₀} {k' l' : ppi (B ∘ f) b₀'} (p : b₀' =[respect_pt f] b₀)
    (q : ppi_functor_left f p k ~* k') (r : ppi_functor_left f p l ~* l') :
    (q pt)⁻¹ ⬝ transport (λx, k x = l x) (respect_pt f)⁻¹ (respect_pt k ⬝ (respect_pt l)⁻¹) ⬝ r pt =
    respect_pt k' ⬝ (respect_pt l')⁻¹ :=
  begin
    exact sorry
  end

  definition ppi_eq_equiv_natural_left_gen {A' A : Type*} {B : A → Type} {f : A' →* A}
    {b₀ : B pt} {b₀' : B (f pt)} {k l : ppi B b₀} {k' l' : ppi (B ∘ f) b₀'} (p : b₀' =[respect_pt f] b₀)
    (q : ppi_functor_left f p k ~* k') (r : ppi_functor_left f p l ~* l') :
    hsquare (ap1_gen (ppi_functor_left f p) (eq_of_phomotopy q) (eq_of_phomotopy r))
            (ppi_functor f (λa' s, (q a')⁻¹ ⬝ s ⬝ r a') (ppi_eq_equiv_natural_left_gen_lem p q r))
            phomotopy_of_eq
            phomotopy_of_eq :=
  begin
    intro r, induction r,
    induction f with f f₀, induction A with A a₀, esimp at * ⊢,
    induction p,
    induction k with k k₀,
    induction k₀,
    revert l' r, refine phomotopy_rec_idp' _ _,
    revert k' q, refine phomotopy_rec_idp' _ _,
    --reflexivity,
    exact sorry,
  end

  definition ppi_eq_equiv_natural_left_gen_sigma {A' A : Type*} {B : A → Type} {f : A' →* A}
    {b₀ : B pt} {b₀' : B (f pt)} {k l : ppi B b₀} {k' l' : ppi (B ∘ f) b₀'} (p : b₀' =[respect_pt f] b₀)
    (q : ppi_functor_left f p k ~* k') (r : ppi_functor_left f p l ~* l') :
    Σ(t : (q pt)⁻¹ ⬝ transport (λx, k x = l x) (respect_pt f)⁻¹ (respect_pt k ⬝ (respect_pt l)⁻¹) ⬝ r pt =
    respect_pt k' ⬝ (respect_pt l')⁻¹),
    hsquare (ap1_gen (ppi_functor_left f p) (eq_of_phomotopy q) (eq_of_phomotopy r))
            (ppi_functor f (λa' s, (q a')⁻¹ ⬝ s ⬝ r a') t)
            phomotopy_of_eq
            phomotopy_of_eq :=
  begin
    induction f with f f₀, induction A with A a₀, esimp at * ⊢,
    induction p,
    induction k with k k₀,
    induction k₀,
    revert l' r, refine phomotopy_rec_idp' _ _,
    revert k' q, refine phomotopy_rec_idp' _ _,
    fconstructor,
    exact !con_idp ⬝ !idp_con ⬝ !idp_con ⬝ !idp_con⁻¹ ⬝
      !respect_pt_ppi_functor_left⁻¹ ◾ !respect_pt_ppi_functor_left⁻¹⁻²,
    intro r, induction r,
    transitivity phomotopy.rfl,
    reflexivity,
    exact sorry,
    --transitivity (ppi_functor_left (pmap.mk f idp) ppi.mk k idp ~* ppi.mk k idp),
--    exact _ ⬝ _ ◾ _

  end
  definition loop_pppi_pequiv_natural_left {A' A : Type*} (X : A → Type*) (f :  A' →* A) :
    psquare
      (Ω→ (ppi_compose_right X f))
      (ppi_compose_right (Ω ∘ X) f)
      (loop_pppi_pequiv X)
      (loop_pppi_pequiv (X ∘ f)) :=
  begin
    induction A with A a, induction f with f f₀, esimp at (f, f₀), induction f₀,
    fapply phomotopy.mk,
--    do 2 exact sorry
--(pmap_compose_ppi_ppi_const (λa, pmap_of_map (f a) pt))(pmap_compose_ppi_ppi_const (λa, pmap_of_map (f a) pt))
    { note z := ppi_eq_equiv_natural_left_gen _
        (ppi_compose_pmap_ppi_const X (pmap.mk f idp)) (ppi_compose_pmap_ppi_const X (pmap.mk f idp)),
      exact sorry --exact hvconcat z _
      },
    { exact sorry /-exact !ppi_eq_equiv_natural_gen_refl ◾ (!idp_con ⬝ !ppi_eq_refl)-/ }
  end

  definition loop_ppmap_pequiv2 [constructor] (A B : Type*) : Ω (ppmap A B) ≃* ppmap A (Ω B) :=
  loop_pequiv_loop (pppi_pequiv_ppmap A B)⁻¹ᵉ* ⬝e* loop_pppi_pequiv (λa, B) ⬝e* pppi_pequiv_ppmap A (Ω B)

  definition loop_ppmap_pequiv2_natural_left {A' A : Type*} (B : Type*) (f : A' →* A) :
    psquare
      (Ω→ (ppcompose_right f))
      (ppcompose_right f)
      (loop_ppmap_pequiv2 A B)
      (loop_ppmap_pequiv2 A' B) :=
  begin
    exact sorry
  end

  definition loop_ppmap_pequiv2_natural_right (A : Type*) {B B' : Type*} (f : B →* B') :
    psquare
      (Ω→ (ppcompose_left f))
      (ppcompose_left (Ω→ f))
      (loop_ppmap_pequiv2 A B)
      (loop_ppmap_pequiv2 A B') :=
  begin
    exact sorry
  end

/-

Template for defining an equivalence:

variables {}
definition nar_of_noo [unfold ]
  (x : foo) : bar :=
begin
  induction x,
  { },
  { },
  { },
  { }
end

definition noo_of_nar [unfold ]
  (x : bar) : foo :=
begin
  induction x,
  { },
  { },
  { },
  { }
end

variables ()
definition noo_equiv_nar [constructor] :
  foo ≃ bar :=
equiv.MK nar_of_noo noo_of_nar
  abstract begin
    intro x, induction x,
    { },
    { },
    { },
    { }
  end end
  abstract begin
    intro x, induction x,
    { },
    { },
    { },
    { }
  end end
-- apply eq_pathover_id_right, refine ap_compose nar_of_noo _ _ ⬝ ap02 _ !elim_glue ⬝ph _
-- apply eq_pathover_id_right, refine ap_compose noo_of_nar _ _ ⬝ ap02 _ !elim_glue ⬝ph _

----------------------------------------------------------------------------------------------------
Template for defining a pointed equivalence:

variables {}
definition nar_of_noo' [unfold ]
  (x : foo) : bar :=
begin
  induction x,
  { },
  { },
  { },
  { }
end

definition noo_of_nar' [unfold ]
  (x : bar) : foo :=
begin
  induction x,
  { },
  { },
  { },
  { }
end

variables ()
definition nar_of_noo [constructor] :
  foo →* bar :=
pmap.mk nar_of_noo' idp

definition noo_of_nar [constructor] :
  bar →* foo :=
pmap.mk noo_of_nar' idp

definition noo_pequiv_nar [constructor] :
  foo ≃* bar :=
pequiv.MK (nar_of_noo _) (noo_of_nar _)
  abstract begin

  end end
  abstract begin

  end end
-- apply eq_pathover_id_right, refine ap_compose nar_of_noo _ _ ⬝ ap02 _ !elim_glue ⬝ph _
-- apply eq_pathover_id_right, refine ap_compose noo_of_nar _ _ ⬝ ap02 _ !elim_glue ⬝ph _










-/



/-
  begin
    fapply pequiv_of_equiv,
    { fapply equiv.MK,
      { },
      { },
      { },
      { }},
    { }
  end

  begin
    induction x,
    { },
    { },
    { },
    { }
  end

      induction x,
      { },
      { },
      { },
      { }


-/
