/- Some work to show that the subgroup of a free group is free -/

import ..Spectral.homotopy.fwedge ..Spectral.algebra.free_group ..Spectral.homotopy.EM algebra.graph
       ..Spectral.choice ..Spectral.algebra.free_group

open eq equiv is_equiv fwedge circle trunc pointed pushout is_trunc algebra group EM quotient
     sigma unit is_conn pi sigma.ops function sum choice property prod.ops lift nat fiber decidable
     prod

universe variables u v
set_option formatter.hide_full_terms false
set_option pp.binder_types true
/- move -/

definition InfGroup_Loop [constructor] (X : Type*) : InfGroup :=
InfGroup.mk (Ω X) _

definition Group_Loop [constructor] (X : Type*) [is_trunc 1 X] : Group :=
Group.mk (Ω X) (group_of_inf_group (Ω X))

definition is_maximal {A : Type} [weak_order A] (a : A) : Type :=
Π(b : A), ¬a ≤ b

definition is_chain {A : Type} [weak_order A] (C : A → Prop) : Type :=
Π(a a' : A), C a → C a' → a ≤ a' ∨ a' ≤ a

definition is_prop_chain [instance] {A : Type} {H : weak_order A} (C : A → Prop) :
  is_prop (is_chain C) :=
!is_trunc_pi

definition chain (A : Type.{u}) [weak_order A] : Set.{u+1} :=
trunctype.mk (Σ(C : A → Prop.{u}), is_chain C) !is_trunc_sigma

definition upper_bound {A : Type.{u}} [weak_order A] (C : A → Prop.{u}) (a : A) : Type.{u} :=
Πa', C a' → a' ≤ a

structure prop_weak_order [class] (A : Type) extends weak_order A :=
  (is_prop_le : Πa b, is_prop (le a b))

definition is_prop_le [instance] {A : Type} [prop_weak_order A] (a a' : A) : is_prop (a ≤ a') :=
prop_weak_order.is_prop_le a a'

definition is_prop_upper_bound [instance] {A : Type} [prop_weak_order A] (C : A → Prop) (a : A) :
  is_prop (upper_bound C a) :=
!is_trunc_pi

/- wedge of circles -/
definition VS1' (X : Type) : Type :=
@pquotient punit (λx y, X)

definition VS1 [reducible] (X : Type) : Type* :=
pointed.MK (VS1' X) !Point

definition VS1_functor' [unfold 4] {X X' : Type} (f : X → X') : VS1 X → VS1 X' :=
quotient.functor _ _ id (λu v, f)

definition VS1_functor [constructor] {X X' : Type} (f : X → X') : VS1 X →* VS1 X' :=
pmap.mk (VS1_functor' f) idp

definition VS1_glue {X : Type} (x : X) : pt = pt :> VS1 X :=
eq_of_rel _ x

protected definition VS1.rec [recursor] {A : Type} {P : VS1 A → Type} (Ppt : P pt)
  (Pglue : Π(a : A), Ppt =[VS1_glue a] Ppt) (x : VS1' A) : P x :=
begin
  induction x with u,
  { cases u, exact Ppt },
  { induction a, induction a', apply Pglue }
end

theorem rec_VS1_glue {A : Type} {P : VS1 A → Type} (Ppt : P pt)
  (Pglue : Π(a : A), Ppt =[VS1_glue a] Ppt) (a : A)
    : apd (VS1.rec Ppt Pglue) (VS1_glue a) = Pglue a :=
!rec_eq_of_rel

protected definition VS1.elim [recursor 5] {A : Type} {P : Type} (Ppt : P)
  (Pglue : A → Ppt = Ppt) (x : VS1' A) : P :=
begin
  induction x with u,
  { exact Ppt },
  { apply pathover_of_eq, exact Pglue u }
end

theorem elim_VS1_glue {A : Type} {P : Type} (Ppt : P) (Pglue : A → Ppt = Ppt) (a : A)
    : ap (VS1.elim Ppt Pglue) (VS1_glue a) = Pglue a :=
begin
  apply eq_of_fn_eq_fn_inv !(pathover_constant (VS1_glue a)),
  xrewrite [▸*,-apd_eq_pathover_of_eq_ap,↑VS1.elim,rec_VS1_glue],
end

protected definition VS1.elim_type {X : Type} (Y : Type) (Pglue : X → Y ≃ Y) : VS1 X → Type :=
VS1.elim Y (λx, ua (Pglue x))

theorem elim_type_VS1_glue {X : Type} {Y : Type} (Pglue : X → Y ≃ Y) (x : X) (y : Y)
  : transport (VS1.elim_type Y Pglue) (VS1_glue x) y = Pglue x y :=
begin
  xrewrite [tr_eq_cast_ap_fn, ↑VS1.elim_type, elim_VS1_glue], apply cast_ua
end

theorem elim_type_VS1_glue_inv {X : Type} {Y : Type} (Pglue : X → Y ≃ Y) (x : X) (y : Y)
  : transport (VS1.elim_type Y Pglue) (VS1_glue x)⁻¹ y = (Pglue x)⁻¹ᵉ y :=
begin
  xrewrite [tr_eq_cast_ap_fn, ↑VS1.elim_type, ap_inv, elim_VS1_glue], apply cast_ua_inv
end


lemma is_conn_VS1 [instance] (X : Type) : is_conn 0 (VS1 X) :=
is_conn_zero_pointed'
  begin intro x, induction x using quotient.rec_prop with x, induction x, exact tidp end

section
open list group algebra
definition VS1_code {X : Type.{u}} [decidable_eq X] (x : VS1 X) : Type.{u} :=
begin
  induction x with x,
  { exact dfree_group X },
  { apply ua, exact right_action (dfree_group_inclusion x) }
end

definition VS1_encode {X : Type} [decidable_eq X] (x : VS1 X) (p : pt = x) : VS1_code x :=
transport VS1_code p (@one (dfree_group X) _)

section
local attribute [coercion] InfGroup_of_Group

definition VS1_decode' {X : Type} [decidable_eq X] : dfree_group X →∞g InfGroup_Loop (VS1 X) :=
dfree_group_inf_hom (InfGroup_Loop (VS1 X)) VS1_glue
end

definition VS1_decode {X : Type} [decidable_eq X] (x : VS1 X) (c : VS1_code x) : pt = x :=
begin
  induction x with x,
  { exact VS1_decode' c },
  { apply arrow_pathover_left,
    intro c, apply eq_pathover,
    refine _ ⬝vp ap VS1_decode' (elim_type_VS1_glue _ x c)⁻¹ᵖ,
    refine !ap_constant ⬝ph _ ⬝hp !ap_id⁻¹,
    refine _ ⬝vp (to_respect_mul_inf VS1_decode' c (dfree_group_inclusion x))⁻¹,
    refine _ ⬝vp ap (λx, _ ⬝ x) !dfree_group_inf_hom_inclusion⁻¹,
    apply square_of_eq, exact !idp_con⁻¹ }
end

definition VS1_decode_encode {X : Type} [decidable_eq X] (x : VS1 X) (p : pt = x) :
  VS1_decode x (VS1_encode x p) = p :=
by induction p; reflexivity

definition VS1_encode_decode_pt_gen {X : Type} [decidable_eq X] (x : X) :
  VS1_encode pt (VS1_decode' (dfree_group_inclusion x)) = dfree_group_inclusion x :=
ap (VS1_encode pt) !dfree_group_inf_hom_inclusion ⬝ !elim_type_VS1_glue


definition VS1_encode_decode_pt {X : Type} [decidable_eq X] : Π(c : dfree_group X),
  VS1_encode pt (VS1_decode' c) = c :=
begin
  refine dfree_group.rec_rev _ _, reflexivity,
  intro g v p, refine ap (VS1_encode pt) !to_respect_mul_inf ⬝ _, refine !con_tr ⬝ _,
  refine ap (transport _ _) p ⬝ _,
  induction v with x x,
  refine ap (λx, transport _ x _) !dfree_group_inf_hom_inclusion ⬝ !elim_type_VS1_glue,
  rewrite [rsingleton_inr, to_respect_inv_inf],
  refine ap (λx, transport _ x _) !dfree_group_inf_hom_inclusion⁻² ⬝ !elim_type_VS1_glue_inv
end

end

definition loop_VS1' (X : Type) [decidable_eq X] : Ω (VS1 X) ≃ dfree_group X :=
begin
  apply equiv.MK (VS1_encode pt) (VS1_decode pt),
  { exact VS1_encode_decode_pt },
  { exact VS1_decode_encode pt }
end

definition loop_VS1'_con {X : Type} [decidable_eq X] (p q : Ω (VS1 X)) :
  loop_VS1' X (p ⬝ q) = loop_VS1' X p * loop_VS1' X q :=
preserve_binary_of_inv_preserve (loop_VS1' X) concat mul (to_respect_mul_inf VS1_decode') p q

definition loop_VS1 (X : Type) [decidable_eq X] : Ω (VS1 X) ≃ free_group X :=
loop_VS1' X ⬝e equiv_of_isomorphism (dfree_group_isomorphism X)

definition loop_VS1_con {X : Type} [decidable_eq X] (p q : Ω (VS1 X)) :
  loop_VS1 X (p ⬝ q) = loop_VS1 X p * loop_VS1 X q :=
ap (equiv_of_isomorphism _) (loop_VS1'_con p q) ⬝ !to_respect_mul

section
open susp option
variables {X : Type}
definition susp_of_VS1 [unfold 1] (x : VS1 X) : ⅀ (option X) :=
begin
  induction x with x,
  { exact north },
  { exact merid (some x) ⬝ (merid none)⁻¹ }
end

definition VS1_of_susp [unfold 1] (x : ⅀ (option X)) : VS1 X :=
begin
  induction x with x,
  { exact pt },
  { exact pt },
  { induction x with x, exact idp, exact VS1_glue x }
end

variables (X)
-- definition susp_of_VS1 [constructor] : VS1 X →* ⅀ (option X) :=
-- pmap.mk susp_of_VS1' idp

-- definition VS1_of_susp [constructor] : ⅀ (option X) →* VS1 X :=
-- pmap.mk VS1_of_susp' idp

definition VS1_equiv_susp [constructor] :
  VS1 X ≃ ⅀ (option X) :=
equiv.MK susp_of_VS1 VS1_of_susp
  abstract begin
    intro x, induction x with x,
    { reflexivity },
    { exact merid none },
    { apply eq_pathover_id_right, refine ap_compose susp_of_VS1 _ _ ⬝ ap02 _ !elim_merid ⬝ph _,
      induction x: esimp,
      { exact square_of_eq idp },
      { refine !elim_VS1_glue ⬝ph _, exact whisker_bl _ hrfl }}
  end end
  abstract begin
    intro x, induction x with x,
    { reflexivity },
    { apply eq_pathover_id_right,
      refine ap_compose VS1_of_susp _ _ ⬝
             ap02 _ !elim_VS1_glue ⬝ !ap_con ⬝ !elim_merid ◾ (!ap_inv ⬝ !elim_merid⁻²) ⬝ph hrfl }
  end end

end

lemma is_trunc_VS1 [instance] (X : Type) [decidable_eq X] : is_trunc 1 (VS1 X) :=
is_trunc_succ_succ_of_is_trunc_loop _ _ (is_trunc_equiv_closed_rev _ (loop_VS1 X)) _

definition fundamental_group_VS1 (X : Type) [decidable_eq X] : π₁ (VS1 X) ≃g free_group X :=
fundamental_group_isomorphism (loop_VS1 X) loop_VS1_con

definition EM1_free_group (X : Type) [decidable_eq X] : EM1 (free_group X) ≃* VS1 X :=
EM1_pequiv (fundamental_group_VS1 X)⁻¹ᵍ

definition fibration_free_subgroup {X : Type} [decidable_eq X]
  {G : Group} (φ : G →g free_group X) (x : VS1 X) : Type :=
fiber (EM1_free_group X ∘* EM1_functor φ) x

lemma is_set_fibration_free_subgroup {X : Type} [decidable_eq X]
  {G : Group} (φ : G →g free_group X) (H : is_embedding φ) (x : VS1 X) :
  is_set (fibration_free_subgroup φ x) :=
sorry /- from LES -/

definition covering_space_free_subgroup {X : Type} [decidable_eq X]
  {G : Group} (φ : G →g free_group X) (H : is_embedding φ) (x : VS1 X) : Set :=
trunctype.mk _ (is_set_fibration_free_subgroup φ H x)


/- covering graph from a covering space over a wedge of circles -/
variables {X : Type} [is_set X] {P : VS1 X → Set}
definition covering_graph_rel (P : VS1 X → Set) (y z : P pt) : Type :=
Σ(x : X), transport P (VS1_glue x) y = z

definition is_set_covering_graph_rel (P : VS1 X → Set) (y z : P pt) :
  is_set (covering_graph_rel P y z) :=
!is_trunc_sigma

definition covering_graph' (P : VS1 X → Set) : Type :=
quotient (covering_graph_rel P)

definition covering_graph (P : VS1 X → Set) (p₀ : P pt) : Type* :=
pointed.MK (covering_graph' P) (class_of _ p₀)

definition covering_graph_of_sigma [unfold 3] (x : VS1 X) (y : P x) :
  covering_graph' P :=
begin
  induction x with x,
  { exact class_of _ y },
  { esimp, apply arrow_pathover_constant_right, intro y,
    exact eq_of_rel _ ⟨x, idp⟩ }
end

definition sigma_of_covering_graph [unfold 3] (x : covering_graph' P) : Σx, P x :=
begin
  induction x with y y₁ y₂ v,
  { exact ⟨pt, y⟩ },
  { apply dpair_eq_dpair (VS1_glue v.1), exact pathover_of_tr_eq v.2 }
end

definition covering_graph_equiv (P : VS1 X → Set) : covering_graph' P ≃ Σx, P x :=
begin
  fapply equiv.MK sigma_of_covering_graph (λv, covering_graph_of_sigma v.1 v.2),
  { intro v, induction v with x p, esimp, induction x with x,
    { reflexivity },
    { esimp, apply @pi_pathover_right' _ _ _ _
        (λv, sigma_of_covering_graph (covering_graph_of_sigma v.1 v.2) = v),
      intro y, apply eq_pathover,
      refine ap_compose sigma_of_covering_graph _ _ ⬝ ap02 _ !ap_dpair_eq_dpair_pr ⬝ph _ ⬝hp
        !ap_id⁻¹,
      apply hdeg_square,
      refine ap02 _ (!apd011_eq_apo11_apd ⬝ ap010 apo11_constant_right !rec_eq_of_rel _ ⬝
        !apo11_arrow_pathover_constant_right) ⬝ _,
      refine !ap_con ⬝ !elim_eq_of_rel ◾ !ap_compose'⁻¹ ⬝ _, esimp,
      refine idp ◾ !ap_dpair ⬝ !dpair_eq_dpair_con⁻¹ ⬝ _,
      apply ap (dpair_eq_dpair _),
      exact !pathover_of_tr_eq_idp' ◾o idp ⬝ !pathover_tr_pathover_idp_of_eq }},
  { intro x, induction x with y y₁ y₂ v,
    { reflexivity },
    { induction v with x p, apply eq_pathover_id_right, apply hdeg_square,
      refine ap_compose (λv, covering_graph_of_sigma v.1 v.2) _ _ ⬝ ap02 _ !elim_eq_of_rel ⬝ _,
      refine ap_dpair_eq_dpair_pr covering_graph_of_sigma _ _ ⬝ _, esimp,
      refine !apd011_eq_apo11_apd ⬝ _,
      refine ap010 apo11_constant_right !rec_eq_of_rel _ ⬝ _, esimp,
      refine !apo11_arrow_pathover_constant_right ⬝ _,
      refine idp ◾ ap02 _ (to_right_inv !pathover_equiv_tr_eq _) ⬝ _, induction p, reflexivity }}
end

definition covering_graph_pequiv (P : VS1 X → Set) (p₀ : P pt) :
  covering_graph P p₀ ≃* psigma_gen P p₀ :=
pequiv_of_equiv (covering_graph_equiv P) idp

definition covering_graph_covering_space {X : Type} [decidable_eq X]
  {G : Group} (φ : G →g free_group X) (H : is_embedding φ) :
  covering_graph (covering_space_free_subgroup φ H) fiberpt ≃* EM1 G :=
!covering_graph_pequiv ⬝e* psigma_fiber_pequiv (EM1_free_group X ∘* EM1_functor φ)

/- Some basic properties about graphs -/

namespace paths

-- inductive paths {A : Type} (R : A → A → Type) : A → A → Type :=
-- | nil {} : Π{a : A}, paths R a a
-- | cons   : Π{a₁ a₂ a₃ : A} (r : R a₂ a₃), paths R a₁ a₂ → paths R a₁ a₃

/- based paths induction -/
definition paths.rec' [recursor] {A : Type} {R : A → A → Type} {a : A}
  {P : Π⦃a'⦄, paths R a a' → Type}
  (Pnil : P nil) (Pcons : Π⦃a₂ a₃ : A⦄ (r : R a₂ a₃) {q : paths R a a₂}, P q → P (r::q))
  {a' : A} (p : paths R a a') : P p :=
begin
  induction p with a a₁ a₂ a₃ r p IH,
  { exact Pnil },
  { apply Pcons, apply IH, exact Pnil, exact Pcons }
end

variables {A A' : Type} {R : A → A → Type} {R' : A' → A' → Type} {a₁ a₂ a₃ a₄ a₁' a₂' : A}

open prod prod.ops
definition cons_code {A : Type.{u}} {R : A → A → Type.{v}} {a₁ a₂ a₃ : A}
  (r : R a₂ a₃) (p : paths R a₁ a₂) (p' : paths R a₁ a₃) : Type.{max u v} :=
begin
  induction p' with a₃ a₁ a₂' a₃ r' p' codep',
  { exact lift empty },
  { exact ⟨a₂, (r, p)⟩ = ⟨a₂', (r', p')⟩ }
end

definition cons_encode {A : Type} {R : A → A → Type} {a₁ a₂ a₃ : A} {r : R a₂ a₃}
  {p : paths R a₁ a₂} {p' : paths R a₁ a₃} (h : r::p = p') : cons_code r p p' :=
begin
  induction h, exact idp
end

definition cons_dinj {A : Type} {R : A → A → Type} {a₁ a₂ a₂' a₃ : A} {r : R a₂ a₃} {r' : R a₂' a₃}
  {p : paths R a₁ a₂} {p' : paths R a₁ a₂'} (h : r::p = r'::p') : ⟨a₂, (r, p)⟩ = ⟨a₂', (r', p')⟩ :=
cons_encode h

definition cons_dinj1 {A : Type} {R : A → A → Type} {a₁ a₂ a₂' a₃ : A} {r : R a₂ a₃} {r' : R a₂' a₃}
  {p : paths R a₁ a₂} {p' : paths R a₁ a₂'} (h : r::p = r'::p') : ⟨a₂, r⟩ = ⟨a₂', r'⟩ :=
begin
  note z := cons_dinj h,
  refine sigma_eq z..1 (prod_pathover_equiv _ _ _ (sigma.eq_pr2 z)).1
end

definition cons_dinj2 {A : Type} {R : A → A → Type} {a₁ a₂ a₂' a₃ : A} {r : R a₂ a₃} {r' : R a₂' a₃}
  {p : paths R a₁ a₂} {p' : paths R a₁ a₂'} (h : r::p = r'::p') : ⟨a₂, p⟩ = ⟨a₂', p'⟩ :=
begin
  note z := cons_dinj h,
  refine sigma_eq z..1 (prod_pathover_equiv _ _ _ (sigma.eq_pr2 z)).2
end

definition map (f : A → A') (g : Π⦃a a'⦄, R a a' → R' (f a) (f a')) ⦃a₁ a₂ : A⦄
  (p : paths R a₁ a₂) : paths R' (f a₁) (f a₂) :=
begin
  induction p with a a₁ a₂ a₃ r p IH,
  { exact nil },
  { exact g r :: IH }
end

definition mapr {R' : A → A → Type} (g : Π⦃a a'⦄, R a a' → R' a a') ⦃a₁ a₂ : A⦄
  (p : paths R a₁ a₂) : paths R' a₁ a₂ :=
map id g p

definition map_append (f : A → A') (g : Π⦃a a'⦄, R a a' → R' (f a) (f a')) ⦃a₁ a₂ a₃ : A⦄
  (q : paths R a₂ a₃) (p : paths R a₁ a₂) : map f g (q ++ p) = map f g q ++ map f g p :=
begin
  induction q with a a₁ a₂ a₃ r q IH,
  { reflexivity },
  { refine ap (cons _) (IH p) }
end

definition mapr_append {R' : A → A → Type} (g : Π⦃a a'⦄, R a a' → R' a a') ⦃a₁ a₂ a₃ : A⦄
  (q : paths R a₂ a₃) (p : paths R a₁ a₂) : mapr g (q ++ p) = mapr g q ++ mapr g p :=
!map_append

definition subgraph (T : Π⦃a₁ a₂ : A⦄, R a₁ a₂ → Type) (a₁ a₂ : A) : Type :=
Σ(e : R a₁ a₂), T e

-- definition eq_of_path (p : paths E v₁ v₂) : class_of E v₁ = class_of E v₂ :=

-- definition eq_of_upath (p : upaths E v₁ v₂) : class_of E v₁ = class_of E v₂ :=

definition eqrealize {f : A → A'} (g : Π⦃a a'⦄, R a a' → f a = f a')
  ⦃a a' : A⦄ (l : paths R a a') : f a = f a' :=
realize _ g (λx, idp) (λx y z q r, q ⬝ r) l

theorem eqrealize_append {f : A → A'} (g : Π⦃a a'⦄, R a a' → f a = f a')
  ⦃a₁ a₂ a₃ : A⦄ (l₂ : paths R a₂ a₃) (l₁ : paths R a₁ a₂) :
  eqrealize g (l₂ ++ l₁) = eqrealize g l₁ ⬝ eqrealize g l₂ :=
realize_append begin intros, apply con.assoc end begin intros, reflexivity end l₂ l₁

theorem eqrealize_singleton {f : A → A'} (g : Π⦃a a'⦄, R a a' → f a = f a')
  ⦃a₁ a₂ : A⦄ (r : R a₁ a₂) : eqrealize g [r] = g r :=
!idp_con

theorem eqrealize_pair {f : A → A'} (g : Π⦃a a'⦄, R a a' → f a = f a')
  ⦃a₁ a₂ a₃ : A⦄ (r₂ : R a₂ a₃) (r₁ : R a₁ a₂) : eqrealize g [r₂, r₁] = g r₁ ⬝ g r₂ :=
whisker_right _ (eqrealize_singleton g r₁)

definition realize_mapr {P R' : A → A → Type} (f : Π⦃a a'⦄, R' a a' → P a a') (ρ : Πa, P a a)
    (c : Π⦃a₁ a₂ a₃⦄, P a₁ a₂ → P a₂ a₃ → P a₁ a₃)
    (g : Π⦃a a'⦄, R a a' → R' a a') ⦃a₁ a₂ : A⦄ (p : paths R a₁ a₂) :
    realize P f ρ c (mapr g p) = realize P (λa a' e, f (g e)) ρ c p :=
begin
  induction p with a a₁ a₂ a₃ r p IH,
  { reflexivity },
  { refine ap (λx, c x _) IH }
end

definition eqrealize_mapr {R' : A → A → Type} {f : A → A'} (g : Π⦃a a'⦄, R' a a' → f a = f a')
    (h : Π⦃a a'⦄, R a a' → R' a a') ⦃a₁ a₂ : A⦄ (p : paths R a₁ a₂) :
    eqrealize g (mapr h p) = eqrealize (λa a' e, g (h e)) p :=
!realize_mapr

definition eqrealize_constant {a₀' : A'} ⦃a₁ a₂ : A⦄ (p : paths R a₁ a₂) :
    eqrealize (λa a' e, idpath a₀') p = idp :=
begin
  induction p with a a₁ a₂ a₃ r p IH,
  { reflexivity },
  { exact IH }
end

-- undirected graph
definition undir (R : A → A → Type) (a₁ a₂ : A) : Type :=
R a₁ a₂ ⊎ R a₂ a₁

definition decidable_eq_undir (R : A → A → Type.{v}) [Πa a', decidable_eq (R a a')] (a a' : A) :
  decidable_eq (undir R a a') :=
decidable_eq_sum _ _

definition upaths (R : A → A → Type) (a₁ a₂ : A) : Type := paths (undir R) a₁ a₂

definition undir_symm (p : undir R a₁ a₂) : undir R a₂ a₁ :=
sum.elim p inr inl

definition usymm (p : upaths R a₁ a₂) : upaths R a₂ a₁ :=
begin
  induction p with a a₁ a₂ a₃ r p IH,
  { exact nil },
  { exact IH ++ [undir_symm r] }
end

definition umapr {R' : A → A → Type} (g : Π⦃a a'⦄, R a a' → R' a a') ⦃a₁ a₂ : A⦄
  (p : upaths R a₁ a₂) : upaths R' a₁ a₂ :=
mapr (λa a', !@g +→ !@g) p

definition umapr_append {R' : A → A → Type} (g : Π⦃a a'⦄, R a a' → R' a a') ⦃a₁ a₂ a₃ : A⦄
  (q : upaths R a₂ a₃) (p : upaths R a₁ a₂) : umapr g (q ++ p) = umapr g q ++ umapr g p :=
!mapr_append

definition ueqrealize {f : A → A'} (g : Π⦃a a'⦄, R a a' → f a = f a')
  ⦃a a' : A⦄ (l : upaths R a a') : f a = f a' :=
eqrealize (λa a', sum.rec (λe, g e) (λe, (g e)⁻¹)) l

definition ueqrealize_umapr {R' : A → A → Type} {f : A → A'} (g : Π⦃a a'⦄, R' a a' → f a = f a')
    (h : Π⦃a a'⦄, R a a' → R' a a') ⦃a₁ a₂ : A⦄ (p : upaths R a₁ a₂) :
    ueqrealize g (umapr h p) = ueqrealize (λa a' e, g (h e)) p :=
begin
  refine !eqrealize_mapr ⬝ ap (λx, eqrealize x _) (eq_of_homotopy3 _),
  -- we could get rid of the function extensionality on previous line
  intros a a' r, induction r with r r: reflexivity
end

theorem ueqrealize_append {f : A → A'} (g : Π⦃a a'⦄, R a a' → f a = f a')
  ⦃a₁ a₂ a₃ : A⦄ (l₂ : upaths R a₂ a₃) (l₁ : upaths R a₁ a₂) :
  ueqrealize g (l₂ ++ l₁) = ueqrealize g l₁ ⬝ ueqrealize g l₂ :=
eqrealize_append _ l₂ l₁

theorem ueqrealize_symm {f : A → A'} (g : Π⦃a a'⦄, R a a' → f a = f a')
  ⦃a₁ a₂ : A⦄ (l : upaths R a₁ a₂) :
  ueqrealize g (usymm l) = (ueqrealize g l)⁻¹ :=
begin
  induction l with a a₁ a₂ a₃ r p IH,
  { reflexivity },
  { refine !eqrealize_append ⬝ (!eqrealize_singleton ⬝ _) ◾ IH ⬝ !con_inv⁻¹,
    induction r, reflexivity, exact !inv_inv⁻¹ }
end

definition ueqrealize_constant {a₀' : A'} ⦃a₁ a₂ : A⦄ (p : upaths R a₁ a₂) :
    ueqrealize (λa a' e, idpath a₀') p = idp :=
begin
  induction p with a a₁ a₂ a₃ r p IH,
  { reflexivity },
  { refine IH ◾ _, induction r: reflexivity }
end

inductive is_reduced : Π{a₁ a₂ : A}, upaths R a₁ a₂ → Type :=
| nil       : Π{a : A} , is_reduced (@nil A _ a)
| singleton : Π{a₁ a₂ : A} (r : undir R a₁ a₂), is_reduced [r]
| cons      : Π{a₁ a₂ a₃ a₄ : A} {s : undir R a₃ a₄} {r : undir R a₂ a₃} {p : upaths R a₁ a₂},
  ⟨a₂, undir_symm r⟩ ≠ ⟨a₄, s⟩ → is_reduced (r::p) → is_reduced (s::r::p)

-- reduced path
definition rpaths (R : A → A → Type) (a₁ a₂ : A) : Type :=
Σ(p : upaths R a₁ a₂), is_reduced p

end paths
open paths
/- reduced paths and reducing paths -/
definition unique_reduced_paths {V : Set} (E : V → V → Type) : Type :=
Πv v', is_prop (rpaths E v v')

definition is_prop_unique_reduced_paths {V : Set} (E : V → V → Type) :
  is_prop (unique_reduced_paths E) :=
!is_trunc_pi


definition is_reduced_invert {V : Set} {E : V → V → Type}
  {v₁ v₃ v₄ : V} (e : undir E v₃ v₄) {p : upaths E v₁ v₃} : is_reduced (e::p) → is_reduced p :=
begin
  assert H : Πe', e::p=e' → is_reduced e' → is_reduced p,
  { intros e' H He', induction He' with v v₁ v₂ e' v₁ v₂ v₃' v₄ e' e'' p' Hneq Hr IH,
    { contradiction },
    { refine transport (λz, @is_reduced V E _ z.1 z.2) _ !is_reduced.nil,
      exact cons_dinj2 H⁻¹ },
    { refine transport (λz, @is_reduced V E _ z.1 z.2) _ Hr, exact cons_dinj2 H⁻¹ }},
  exact H _ idp
end

definition rnil {V : Set} {E : V → V → Type} {v : V} : rpaths E v v :=
⟨[], !is_reduced.nil⟩

definition rcons {V : Set} {E : V → V → Type} (H : Πv, decidable_eq (Σv', undir E v v'))
  {v₁ v₃ v₄ : V} (e : undir E v₃ v₄) (p : upaths E v₁ v₃) : upaths E v₁ v₄ :=
begin
  cases p with x x v₂ x e' p',
  { exact [e] },
  { exact if q : ⟨v₂, undir_symm e'⟩ = ⟨v₄, e⟩
          then transport (upaths E v₁) q..1 p'
          else e::e'::p' }
end

definition is_reduced_rcons {V : Set} {E : V → V → Type}
  (H : Πv, decidable_eq (Σv', undir E v v'))
  {v₁ v₃ v₄ : V} (e : undir E v₃ v₄) {p : upaths E v₁ v₃} (Hp : is_reduced p) :
  is_reduced (rcons H e p) :=
begin
  cases p with x x v₂ x e' p', apply paths.is_reduced.singleton,
  apply dite (⟨v₂, undir_symm e'⟩ = ⟨v₄, e⟩): intro q,
  { apply transport paths.is_reduced (dite_true q _)⁻¹,
    exact transporto (@is_reduced V E v₁) !pathover_tr (is_reduced_invert _ Hp) },
  exact transport is_reduced (dite_false q)⁻¹ (is_reduced.cons q Hp)
end

definition urealize_rcons {V : Set} {E : V → V → Type} {X : Type}
  (H : Πv, decidable_eq (Σv', undir E v v')) {f : V → X} (g : Π⦃v v'⦄, E v v' → f v = f v')
  {v₁ v₃ v₄ : V} (e : undir E v₃ v₄) (p : upaths E v₁ v₃) :
  ueqrealize g (rcons H e p) = ueqrealize g (e::p) :=
begin
  cases p with x x v₂ x e' p', reflexivity,
  apply dite (⟨v₂, undir_symm e'⟩ = ⟨v₄, e⟩): intro q,
  { refine ap (λx, ueqrealize g x) (dite_true q _) ⬝ _,
    revert v₄ e q, refine eq.rec_sigma _ _,
    refine idp ◾ _⁻¹ ⬝ !con.assoc⁻¹,
    induction e', apply con.right_inv, apply con.left_inv },
  exact ap (λx, ueqrealize g x) (dite_false q)
end

definition reduce_path' {V : Set} {E : V → V → Type} (H : Πv, decidable_eq (Σv', undir E v v'))
  {v v' : V} (p : upaths E v v') : upaths E v v' :=
begin
  induction p with a a₁ a₂ a₃ e p redp,
  { exact nil },
  { exact rcons H e redp }
end

definition is_reduced_reduce_path {V : Set} {E : V → V → Type}
  (H : Πv, decidable_eq (Σv', undir E v v')) {v v' : V} (p : upaths E v v') :
  is_reduced (reduce_path' H p) :=
begin
  intros, induction p with a a₁ a₃ a₄ e p IH, apply paths.is_reduced.nil,
  apply is_reduced_rcons, exact IH
end

definition reduce_path {V : Set} {E : V → V → Type} (H : Πv, decidable_eq (Σv', undir E v v'))
  {v v' : V} (p : upaths E v v') : rpaths E v v' :=
⟨reduce_path' H p, is_reduced_reduce_path H p⟩

definition ueqrealize_reduce_path {V : Set} {E : V → V → Type} {X : Type}
  (H : Πv, decidable_eq (Σv', undir E v v'))
  {f : V → X} (g : Π⦃v v'⦄, E v v' → f v = f v')
  {v v' : V} (p : upaths E v v') : ueqrealize g (reduce_path H p).1 = ueqrealize g p :=
begin
  induction p with a a₁ a₃ a₄ e p IH, reflexivity,
  refine !urealize_rcons ⬝ whisker_right _ IH,
end

definition ueqrealize_loop {V : Set} {E : V → V → Type} {X : Type}
  (H : Πv, decidable_eq (Σv', undir E v v'))
  (H₂ : unique_reduced_paths E)
  {f : V → X} (g : Π⦃v v'⦄, E v v' → f v = f v')
  {v : V} (p : upaths E v v) : ueqrealize g p = idp :=
(ueqrealize_reduce_path H g p)⁻¹ ⬝
ap (λ(p : rpaths E v v), ueqrealize g p.1) (@is_prop.elim _ (H₂ v v) _ rnil)


/- definition of spanning tree of a graph -/

structure spanning_tree {V : Set} (E : V → V → Set) : Type :=
  (tree : Π⦃v v'⦄, E v v' → Prop)
  (decT : Π⦃v v'⦄ (e : E v v'), decidable (tree e))
  (spanning : Πv v', upaths (subgraph tree) v v')
  (is_tree : unique_reduced_paths (subgraph tree))

-- structure spanning_tree₂ {V : Set} (E : V → V → Set) : Type :=
--   (T : V → V → Set)
--   (decT : Πv v', decidable (T v v'))
--   (incl : Π⦃v v'⦄, T v v' → E v v')
--   (spanning : Πv v', ∥paths T v v'∥)
--   (tree : Π⦃v v'⦄ (e : T v v') (p : paths T v v') , paths.mem e p)

attribute [coercion] spanning_tree.tree
attribute [instance] spanning_tree.decT

open spanning_tree
variables {V : Set.{u}} {v₀ v₁ v₂ : V} {E : V → V → Set} {T : spanning_tree E}
definition spanning' (T : spanning_tree E) (v₁ v₂ : V) : upaths E v₁ v₂ :=
umapr (λv v', pr1) (spanning T v₁ v₂)

/- constructing a maximal subtree from the axiom of choice -/

definition conn_of_is_conn_quotient (E : V → V → Set) (H : is_conn 0 (quotient E)) (v v' : V) :
  ∥upaths E v v'∥ :=
sorry

/- Some properties of AC -/
definition ACtype : Type :=
Π(X : Type.{u}) (Y : X → Type.{u}), is_set X → (Πx, is_set (Y x)) → is_equiv (unchoose -1 Y)

definition LEMtype : Type := Π⦃X : Type.{u}⦄, is_prop X → decidable X

definition Zorntype : Type := Π⦃A : Type.{u}⦄ (H : is_set A) (s : prop_weak_order A)
  (ccc : Π(C : chain A), ∃a, upper_bound C.1 a), ∃(a : A), is_maximal a

definition LEM_of_AC (AC : ACtype.{u}) : LEMtype.{u} :=
sorry

definition LEM_of_LEM_up (LEM : LEMtype.{max u v}) : LEMtype.{u} :=
sorry

definition Hartog_lemma (A : Type) : Σ(B : Type) (R : B → B → Type),
  well_founded R × Π(f : B → A), ∃(b b' : B), f b = f b' :=
sorry

definition pimage {A B : Type} (f : A → B) (s : property A) : property B :=
{b : B | ∃a, a ∈ s × f a = b }

definition uimage {A : Type.{u}} {B : Type.{v}} (f : A → B) : property B :=
pimage f univ.{u 0}

definition is_succ_of {A : Type} (R : A → A → Type) (a a2 : A) : Type :=
Πa3, R a3 a → a3 = a2 ⊎ R a3 a2

definition is_succ {A : Type} (R : A → A → Type) (a : A) : Type :=
∃a2, is_succ_of R a a2

definition is_limit {A : Type} (R : A → A → Type) (a : A) : Type :=
Πa2, R a2 a → ∃a3, R a2 a3 × R a3 a

definition downset {A : Type} (R : A → A → Type) (a : A) : Type :=
Σa2, R a2 a


/-definition well_founded.elim2 {B C : Set.{u}} (R : B → B → Prop.{u}) [Hwf : well_founded R]
  (H : Πb, is_succ R b ⊎ is_limit R b) (HB : decidable_eq B) (G : property.{u u} C → C) : B → C :=
begin
  assert P : Πb, is_prop (Σ(g : downset R b → C), (Π(x : downset R b), g x = G (pimage g {b' | R b'.1 x.1}))),
  { intro b, apply is_prop.mk, intro v v', apply subtype_eq, apply eq_of_homotopy, intro b,  },
  assert f : Π(b : B), Σ(g : downset R b → C), (Π(x : downset R b), g x = G (pimage g {b' | R b'.1 x.1})),
  { refine well_founded.fix _, exact R, exact _,
    intro b f, apply sum.elim (H b): intro h,
    { },
    { }


}

end-/

/-definition well_founded.rec2 {B C : Type.{u}} (R : B → B → Prop.{u}) [Hwf : well_founded R]
  (P : property C → Type.{u}) (H : Πb, decidable (is_succ R b))
  (G : property C → C) (HG : Πs, P s → P (insert (G s) s)) : Σ(f : B → C), P (uimage f) :=
begin
  assert f : Π(b : B), Σ(g : downset R b → C), (Π(x : downset R b), g x = G (pimage g {b' | R b'.1 x.1})),
  { refine well_founded.fix _, exact R, exact _,
    intro b f,
    apply @dite _ (H b),
    -- intro b f, fconstructor, intro x, induction x with b' r,
    -- induction f b' r with g Hg,

}
  -- exact R, exact _,
  -- intro b' H' haspred, induction haspred with b'' p,
  -- note z := F b' b'' (uimage (λ(x : Σy, R y b' × is_succ R y), H' x.1 x.2.1 x.2.2)) p,

end-/

/-definition well_founded.rec {B C : Type} (R : B → B → Type) [Hwf : well_founded R]
  (P : property C → Type) (H : Πb, decidable (is_succ R b))
  (F : Πx (f : (Σy, R y x) → C), P (uimage f) → Σ(c : C), P (insert c (uimage f))) :
  Σ(f : B → C), P (uimage f) :=
begin
  assert f : Π(b : B), Σ(s : property C), P s,
  { refine well_founded.fix _, exact R, exact _,
  intro b f,
  apply @dite _ (H b): intro H2,
  { induction H2 with b' H, exact sorry }, exact sorry },

  -- intro b f,
  -- exact pr1 (F b _ _)
end-/

/-definition injection {A B : Type} [prop_weak_order A] (R : B → B → Type) [well_founded R]
  (f : Π(C : chain A), Σa, upper_bound C.1 a) : Σ(f : A → B), Σ(a : A), sorry :=
begin
  -- refine well_founded.fix _, exact R, exact _,
  -- intro b H,
exact sorry
end-/

definition Zorn_of_AC : ACtype.{u+1} → Zorntype.{u} :=
begin
  intros AC A H s ccc,
  assert LEM : LEMtype.{u}, exact LEM_of_LEM_up (LEM_of_AC AC),
  apply double_neg_elim (LEM _),
  intro nH,
  assert H1 : Π(C : chain A), is_set (lift (Σ(a : A), upper_bound C.1 a)),
    exact _,
  note f := @is_equiv.inv _ _ _ (AC _ _ _ H1)
    (λC, begin induction ccc C with x, exact tr (lift.up x) end),
  --  induction f with f₀,
  -- assert f : Π(C : chain A), Σa, upper_bound C.1 a, exact λC, lift.down (f₀ C), clear f₀ H1,
  -- clear ccc,
  -- induction Hartog_lemma A with B x, induction x with R x, induction x with HR Hf,
  exact sorry
end

structure subforest {V : Set.{u}} (E : V → V → Set.{u}) : Type :=
  (tree : Π⦃v v'⦄, E v v' → Prop.{u})
  (decT : Π⦃v v'⦄ (e : E v v'), decidable (tree e))
  (is_tree : unique_reduced_paths (subgraph tree))

attribute [coercion] subforest.tree
attribute [instance] subforest.decT

local attribute [instance] is_trunc_decidable is_prop_unique_reduced_paths

definition subforest.sigma_char (E : V → V → Set.{u}) :
  subforest E ≃ Σ(T : Π⦃v v'⦄, E v v' → Prop.{u}), (Π⦃v v'⦄ (e : E v v'), decidable (T e)) ×
    unique_reduced_paths (subgraph T) :=
equiv.MK (λT, ⟨subforest.tree T, (subforest.decT T, subforest.is_tree T)⟩)
         (λX, subforest.mk X.1 X.2.1 X.2.2)
         begin intro X, induction X with T p, induction p, reflexivity end
         begin intro T, induction T, reflexivity end

definition is_embedding_tree (E : V → V → Set) : is_embedding (@subforest.tree V E) :=
begin
  apply is_embedding_compose sigma.pr1 (subforest.sigma_char E),
  apply is_embedding_pr1, apply is_embedding_of_is_equiv
end

definition is_set_subforest (E : V → V → Set.{u}) : is_set (subforest E) :=
have H1 : is_set (Π⦃v v'⦄, E v v' → Prop.{u}), from _,
have H2 : Π(T : Π⦃v v'⦄, E v v' → Prop.{u}), is_prop ((Π⦃v v'⦄ (e : E v v'), decidable (T e)) ×
    unique_reduced_paths (subgraph T)), from _,
@is_trunc_equiv_closed_rev _ _ 0 (subforest.sigma_char E)
  (@is_trunc_sigma _ _ _ H1 (λT, @is_trunc_succ _ _ (H2 T)))

definition prop_weak_order_property [instance] (A : Type.{u}) : prop_weak_order.{u+1} (property.{u u} A) :=
⦃ prop_weak_order, le := λs t, lift (s ⊆ t),
  le_refl := λa, up (subproperty.refl a),
  le_trans := λa b c, lift_functor2 subproperty.trans,
  le_antisymm := λa b h k, subproperty.antisymm (down h) (down k),
  is_prop_le := _ ⦄

definition prop_weak_order_pi [instance] {A : Type} (B : A → Type) [Πa, prop_weak_order (B a)] :
  prop_weak_order (Πa, B a) :=
⦃ prop_weak_order, le := λf g, Πa, f a ≤ g a,
  le_refl := λf a, le.refl (f a),
  le_trans := λf g h H K a, le.trans (H a) (K a),
  le_antisymm := λf g H K, eq_of_homotopy (λa, le.antisymm (H a) (K a)),
  is_prop_le := _ ⦄

definition prop_weak_order_embedding {A B : Type} (f : A → B) (H : is_embedding f)
  [prop_weak_order B] : prop_weak_order A :=
⦃ prop_weak_order, le := λa a', f a ≤ f a',
  le_refl := λa, le.refl (f a),
  le_trans := λa a' a'', le.trans,
  le_antisymm := λa a' H K, is_injective_of_is_embedding (le.antisymm H K),
  is_prop_le := _ ⦄

definition prop_weak_order_subforest [instance] (E : V → V → Set) : prop_weak_order (subforest E) :=
@(prop_weak_order_embedding subforest.tree (is_embedding_tree E))
  (@prop_weak_order_pi _ _ (λa, @prop_weak_order_pi _ _ (λa, !prop_weak_order_property)))

definition spanning_tree_of_AC {V : Set.{u}} (AC : ACtype.{u+2}) (E : V → V → Set.{u})
  (H : Πv v', ∥upaths E v v'∥) : ∥spanning_tree.{u u u} E∥ :=
begin
  assert LEM : LEMtype.{u+1}, exact LEM_of_LEM_up (LEM_of_AC AC),
  assert Zorn : Zorntype.{u+1}, exact Zorn_of_AC AC,
  assert H1 : trunctype.carrier (∃(T : subforest E), is_maximal T),
  { refine Zorn (is_set_subforest E) (prop_weak_order_subforest E) _,
    intro C, exact sorry },
  refine exists.elim H1 _, clear H1, intro T HT,
  refine tr (spanning_tree.mk T _ _ (subforest.is_tree T)),
  intro v v', exact sorry
end

/- collapsing a maximal subtree -/

definition nonvertices (T : spanning_tree E) : Type :=
Σ(v v' : V) (e : E v v'), ¬T e

definition decidable_eq_nonvertices (T : spanning_tree E)
  [decidable_eq V] [Πv v', decidable_eq (E v v')] : decidable_eq (nonvertices T) :=
have Πv v' (e : E v v'), decidable_eq (¬ T e), from λv v' e, decidable_eq_of_is_prop _,
decidable_eq_sigma _

-- definition is_set_nonvertices (T : spanning_tree E)
--   [decidable_eq V] [Πv v', decidable_eq (E v v')] : decidable_eq (nonvertices T) :=

definition set_of_nonvertices (T : spanning_tree E) : Set :=
trunctype.mk (nonvertices T) !is_trunc_sigma

definition eq_of_path (p : paths E v₁ v₂) : class_of E v₁ = class_of E v₂ :=
eqrealize (eq_of_rel _) p

definition eq_of_upath (p : upaths E v₁ v₂) : class_of E v₁ = class_of E v₂ :=
ueqrealize (eq_of_rel _) p

lemma elim_eq_of_upath {P : Type} (Pc : V → P)
  (Pp : Π⦃v v' : V⦄ (H : E v v'), Pc v = Pc v') {v v' : V} (p : upaths E v v')
  : ap (quotient.elim Pc Pp) (eq_of_upath p) = ueqrealize Pp p :=
begin
  induction p with a a₁ a₂ a₃ r p IH,
  { reflexivity },
  { refine !ap_con ⬝ IH ◾ _, induction r with r r,
    { apply elim_eq_of_rel },
    { exact !ap_inv ⬝ !elim_eq_of_rel⁻² }}
end

definition VS1_of_quotient [unfold 4] (T : spanning_tree E) (x : quotient E) :
  VS1 (nonvertices T) :=
begin
  induction x with v v₁ v₂ e,
  { exact pt },
  { exact if h : T e then idp else VS1_glue ⟨v₁, v₂, e, h⟩ }
end

definition quotient_of_VS1 [unfold 5] (T : spanning_tree E) (v₀ : V) (x : VS1 (nonvertices T)) :
  quotient E :=
begin
  induction x with H,
  { exact class_of _ v₀ },
  { exact eq_of_upath !(spanning' T) ⬝ eq_of_rel _ H.2.2.1 ⬝ eq_of_upath !(spanning' T) }
end

definition VS1_of_quotient_tree {v₁ v₂ : V} (e : paths (undir (subgraph (tree T))) v₁ v₂) :
  ap (VS1_of_quotient T) (eq_of_upath (umapr (λv v', pr1) e)) = idpath pt :=
begin
  refine !elim_eq_of_upath ⬝ !ueqrealize_umapr ⬝ _,
  refine ap (λx, ueqrealize x _) (eq_of_homotopy3 (λa a' e', dite_true e'.2 _)) ⬝ _,
  apply ueqrealize_constant
end

definition eq_of_upath_irrel {v : V} (e : paths (undir (subgraph (tree T))) v v)
  [HV : decidable_eq V] [HE : Πv v', decidable_eq (E v v')] :
  eq_of_upath (umapr (λv v', pr1) e) = idp :=
begin
  refine !ueqrealize_umapr ⬝ _,
  apply ueqrealize_loop,
  { intro v, apply @decidable_eq_sigma, intro v', apply decidable_eq_undir,
    intro v₁ v₂, apply decidable_eq_sigma, intro e, apply decidable_eq_of_is_prop },
  apply spanning_tree.is_tree
end

definition quotient_equiv_VS1 [constructor] (HV : decidable_eq V)
  (HE : Πv v', decidable_eq (E v v')) (v₀ : V) : quotient E ≃ VS1 (nonvertices T) :=
begin
  apply equiv.MK (VS1_of_quotient T) (quotient_of_VS1 T v₀),
  { intro x, induction x with e,
    { reflexivity },
    { apply eq_pathover, apply hdeg_square,
      refine ap_compose (VS1_of_quotient T) _ _ ⬝ ap02 _ !elim_VS1_glue ⬝ _ ⬝ !ap_id⁻¹,
      refine !ap_con ⬝ (!ap_con ⬝ !VS1_of_quotient_tree ◾ !elim_eq_of_rel) ◾
        !VS1_of_quotient_tree ⬝ !con_idp ⬝ !idp_con ⬝ _,
      induction e with v₁ e2, induction e2 with v₂ e3, induction e3 with e H,
      exact dite_false H }},
  { intro x, induction x with v v₁ v₂ e,
    { exact eq_of_upath !(spanning' T) },
    { apply eq_pathover_id_right,
      refine ap_compose (quotient_of_VS1 T v₀) _ _ ⬝ ap02 _ !elim_eq_of_rel ⬝ph _,
      apply dite (T e): intro h,
      { refine ap02 _ (dite_true h _) ⬝ph _,
        refine !ueqrealize_umapr ⬝pv _ ⬝vp !ueqrealize_umapr⁻¹,
        apply transpose, apply square_of_eq_top, symmetry,
        refine idp ◾ !ueqrealize_symm⁻¹ ⬝ _,
        refine (ueqrealize_append _ (usymm (spanning T v₀ v₂)) (inl ⟨e, h⟩ :: spanning T v₀ v₁))⁻¹ ⬝
          !ueqrealize_umapr⁻¹ ⬝ !eq_of_upath_irrel },
      { refine ap02 _ (dite_false h) ⬝ !elim_VS1_glue ⬝ph _,
        apply move_left_of_bot, apply whisker_tl, refine hrfl ⬝vp _, symmetry,
        refine !ueqrealize_append⁻¹ ⬝ _,
        refine ap (λx, ueqrealize _ x) !umapr_append⁻¹ ⬝ _,
        apply eq_of_upath_irrel }}}
end

definition quotient_pequiv_VS1 [constructor] (HV : decidable_eq V)
  (HE : Πv v', decidable_eq (E v v')) (v₀ : V) :
  pointed.MK (quotient E) (class_of _ v₀) ≃* VS1 (nonvertices T) :=
pequiv_of_equiv (quotient_equiv_VS1 _ _ v₀) idp

/- final statement -/

/- We need the propositional truncation here, since if we have two isomorphisms
  F X ≃ G ≃ F X',
  then the composite need not come from a bijection X ≃ X'
-/
definition is_free (G : Group.{u}) : Prop :=
∃(X : Set.{u}), G ≃g free_group X

definition is_free_isomorphism {G H : Group.{u}} (φ : G ≃g H) (HH : is_free H) : is_free G :=
begin
  refine exists.elim HH _, intro X ψ,
  exact exists.intro X (φ ⬝g ψ)
end

definition is_free_free_group (X : Set) : is_free (free_group X) :=
exists.intro X !isomorphism.refl

definition is_strictly_free (G : Group.{u}) : Prop :=
∃(X : Type.{u}), Σ(H : decidable_eq X), G ≃g free_group X

definition is_strictly_free_isomorphism {G H : Group.{u}} (φ : G ≃g H) (HH : is_strictly_free H) :
  is_strictly_free G :=
begin
  refine exists.elim HH _, intro X Hψ, induction Hψ with H2 ψ,
  exact exists.intro X ⟨H2, (φ ⬝g ψ)⟩
end

definition is_strictly_free_free_group (X : Type) [decidable_eq X] : is_strictly_free (free_group X) :=
exists.intro X ⟨_, !isomorphism.refl⟩

local attribute [instance] decidable_eq_nonvertices
/- todo: weaken AC to be only AC on the required type. add hypotheses of decidable equality on
  - cokernel (cosets) of φ (V) -/
definition reflect_embedding_free_group {G : Group} {X : Type.{u}} [decidable_eq X]
  (φ : G →g free_group X) (Hφ : is_embedding φ) (AC : ACtype.{u+2}) : is_strictly_free G :=
let P : VS1 X → Set.{u} := covering_space_free_subgroup φ Hφ,
    V : Set.{u} := P pt,
    v₀ : V := fiberpt,
    E : V → V → Set := λv v', trunctype.mk (covering_graph_rel P v v') !is_set_covering_graph_rel in
have dV : decidable_eq V, from sorry,
have dE : Πv v', decidable_eq (E v v'), from
  λv v', @decidable_eq_sigma _ _ _ (λx, decidable_eq_of_is_prop _),
have e : quotient E ≃ EM1 G, from equiv_of_pequiv (covering_graph_covering_space φ Hφ),
have is_conn 0 (quotient E), from is_conn_equiv_closed_rev 0 e _,
have T' : ∥spanning_tree E∥, from spanning_tree_of_AC AC E (conn_of_is_conn_quotient E this),
(λx, trunc.elim x T') (assume T : spanning_tree E,
have f : EM1 G ≃* VS1 (nonvertices T), from
  (covering_graph_covering_space φ Hφ)⁻¹ᵉ* ⬝e* quotient_pequiv_VS1 _ _ v₀,
have ψ : G ≃g free_group (nonvertices T), from
  !fundamental_group_EM1⁻¹ᵍ ⬝g homotopy_group_isomorphism_of_pequiv 0 f ⬝g !fundamental_group_VS1,
show is_strictly_free G, from is_strictly_free_isomorphism ψ !is_strictly_free_free_group)

-- definition covering_graph_covering_space {X : Type} [decidable_eq X]
--   {G : Group} (φ : G →g free_group X) (H : is_embedding φ) :
--   covering_graph (covering_space_free_subgroup φ H) fiberpt ≃* EM1 G :=



definition is_free_reflect_embedding {G : Group} {H : Group.{u}} (φ : G →g H)
  (Hφ : is_embedding φ) (HH : is_strictly_free H) (AC : ACtype.{u+2}) : is_strictly_free.{u}
 G :=
begin
  refine exists.elim HH _, intro X Hψ, induction Hψ with H2 ψ,
  exact reflect_embedding_free_group (ψ ∘g φ) (is_embedding_compose ψ φ _ _) AC,
end

definition is_free_subgroup {G : Group} {H : property G} [is_subgroup G H] (HG : is_free G) :
  is_free (subgroup H) :=
sorry
