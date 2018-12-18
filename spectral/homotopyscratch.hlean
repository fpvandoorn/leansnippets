import .EM
open EM eq equiv is_trunc is_equiv pointed function sigma
open group algebra

  definition EMadd1_phomotopy {G : AbGroup} {n : ℕ} {X : Type*} [H : is_trunc (n.+1) X] {f g : EMadd1 G n →* X}
    (h : Ω→ f ~ Ω→ g) : f ~* g :=
  begin
    revert X H f g h, induction n with n IH: intro X H f g h,
    { have H' : is_trunc 1 X, from H, exact EM1_phomotopy h },
    { exact sorry }
  end


-- import .smash_adjoint .dsmash
-- open smash dsmash sigma.ops
-- Author: Floris van Doorn (informal proofs in collaboration with Stefano Piceghello)
namespace dsmash

exit
  variable {A : Type*}
  definition dsmash_arrow_equiv2 [constructor] (B : A → Type*) (C : Type) :
    (⋀ B → C) ≃ Σ(f : Πa, B a → C) (c₀ : C) (p : Πa, f a pt = c₀) (q : Πb, f pt b = c₀), p pt = q pt :=
  begin
    fapply equiv.MK,
    { intro f, exact ⟨λa b, f (dsmash.mk a b), f (dsmash.mk pt pt), λa,
                      ap f (gluel' a pt), λb, ap f (gluer' b pt), ap02 f (!con.right_inv ⬝ !con.right_inv⁻¹)⟩ },
    { intro x, exact dsmash.elim x.1 x.2.1 x.2.1 x.2.2.1 x.2.2.2.1 },
    { intro x, induction x with f x, induction x with c₁ x, induction x with c₀ x, induction x with p₁ p₂,
      apply ap (dpair _), exact (gluel _)⁻¹ᵖ, apply ap (dpair _), apply ap (dpair _), esimp,
      exact pair_eq (eq_of_homotopy (elim_gluel _ _)) (eq_of_homotopy (elim_gluer _ _)) },
    { intro f, apply eq_of_homotopy, intro x, induction x, reflexivity, reflexivity, reflexivity,
      apply eq_pathover, apply hdeg_square, apply elim_gluel,
      apply eq_pathover, apply hdeg_square, apply elim_gluer }
  end

  definition dsmash_arrow_equiv2_inv_pt [constructor]
    (x : Σ(f : Πa, B a → C) (c₁ : C) (c₀ : C), (Πa, f a pt = c₀) × (Πb, f pt b = c₁)) :
    to_inv (dsmash_arrow_equiv B C) x pt = x.1 pt pt :=
  by reflexivity

  open pi

  definition dsmash_pmap_equiv2 (B : A → Type*) (C : Type*) :
    (⋀ B →* C) ≃ dbppmap B (λa, C) :=
  begin
    refine !pmap.sigma_char ⬝e _,
    refine sigma_equiv_sigma_left !dsmash_arrow_equiv ⬝e _,
    refine sigma_equiv_sigma_right (λx, equiv_eq_closed_left _ (dsmash_arrow_equiv_inv_pt x)) ⬝e _,
    refine !sigma_assoc_equiv ⬝e _,
    refine sigma_equiv_sigma_right (λf, !sigma_assoc_equiv ⬝e
      sigma_equiv_sigma_right (λc₁, !sigma_assoc_equiv ⬝e
        sigma_equiv_sigma_right (λc₂, sigma_equiv_sigma_left !sigma.equiv_prod⁻¹ᵉ ⬝e
          !sigma_assoc_equiv) ⬝e
        sigma_assoc_equiv_left _ (sigma_homotopy_constant_equiv pt (λa, f a pt))⁻¹ᵉ ⬝e
        sigma_equiv_sigma_right (λh₁, !sigma_comm_equiv) ⬝e !sigma_comm_equiv) ⬝e
      sigma_assoc_equiv_left _ (sigma_homotopy_constant_equiv pt (f pt))⁻¹ᵉ ⬝e
      sigma_equiv_sigma_right (λh₂,
        sigma_equiv_sigma_right (λr₂,
          sigma_equiv_sigma_right (λh₁, !comm_equiv_nondep) ⬝e !sigma_comm_equiv) ⬝e
        !sigma_comm_equiv) ⬝e
      !sigma_comm_equiv ⬝e
      sigma_equiv_sigma_right (λr,
        sigma_equiv_sigma_left (pi_equiv_pi_right (λb, equiv_eq_closed_right _ r)) ⬝e
        sigma_equiv_sigma_right (λh₂,
          sigma_equiv_sigma !eq_equiv_con_inv_eq_idp⁻¹ᵉ (λr₂,
            sigma_equiv_sigma_left (pi_equiv_pi_right (λa, equiv_eq_closed_right _ r)) ⬝e
            sigma_equiv_sigma_right (λh₁, !eq_equiv_con_inv_eq_idp⁻¹ᵉ)) ⬝e
          !sigma_comm_equiv ⬝e
          sigma_equiv_sigma_right (λh₁, !comm_equiv_nondep)) ⬝e
        !sigma_comm_equiv) ⬝e
      !sigma_comm_equiv ⬝e sigma_equiv_sigma_right (λh₁,
        !sigma_comm_equiv ⬝e sigma_equiv_sigma_right (λh₂,
          !sigma_sigma_eq_right))) ⬝e _,
    refine !sigma_assoc_equiv' ⬝e _,
    refine sigma_equiv_sigma_left (@sigma_pi_equiv_pi_sigma _ _ (λa f, f pt = pt) ⬝e
      pi_equiv_pi_right (λa, !pmap.sigma_char⁻¹ᵉ)) ⬝e _,
    exact !dbpmap.sigma_char⁻¹ᵉ
  end

end dsmash
exit
namespace smash
  -- definition smash_assoc_elim_pequiv (A B C X : Type*) :
  --   ppmap (A ∧ (B ∧ C)) X ≃* ppmap ((A ∧ B) ∧ C) X :=
  -- calc
  --   ppmap (A ∧ (B ∧ C)) X ≃* ppmap (B ∧ C) (ppmap A X) : smash_adjoint_pmap A (B ∧ C) X
  --   ... ≃* ppmap C (ppmap B (ppmap A X)) : smash_adjoint_pmap B C (ppmap A X)
  --   ... ≃* ppmap C (ppmap (A ∧ B) X) : pequiv_ppcompose_left (smash_adjoint_pmap_inv A B X)
  --   ... ≃* ppmap ((A ∧ B) ∧ C) X : smash_adjoint_pmap_inv (A ∧ B) C X

  variables {A B C D E F X X' : Type*}

-- set_option pp.universes true
-- set_option pp.notation false
-- print smash_assoc
-- print pyoneda

-- print ppcompose_left_pcompose
-- print pppcompose

print phomotopy_of_eq
  definition smash_functor_left_natural_middle_pconst (A C B B' : Type*) :
    smash_functor_left_natural_middle A C (pconst B B') =
    !ppcompose_left_pconst ⬝ph* !pvconst_square ⬝hp* !ppcompose_left_pconst ⬝hp*
    !ppcompose_left_phomotopy !smash_functor_pconst_left :=
  begin
    refine _⁻²** ⬝ !symm_symm,
    fapply phomotopy_eq,
    { intro f, exact sorry }, exact sorry
  end

  definition smash_pmap_counit_natural_right_pconst (B C C' : Type*) :
    smash_pmap_counit_natural_right B (pconst C C') =
    !ppcompose_left_pconst ∧~ phomotopy.rfl ⬝ph* !smash_functor_pconst_left ⬝ph* !pvconst_square :=
  sorry

  definition smash_pelim_natural_right_pconst (A B C C' : Type*) :
    smash_pelim_natural_right A B (pconst C C') =
    ppcompose_left_phomotopy !ppcompose_left_pconst ⬝ph* !ppcompose_left_pconst ⬝ph*
    !pvconst_square ⬝hp* !ppcompose_left_pconst :=
  begin
    refine (smash_functor_left_natural_middle_phomotopy A B !ppcompose_left_pconst ⬝
      idp ◾ph* !smash_functor_left_natural_middle_pconst ◾hp* idp) ◾h*
      ap ppcompose_left_psquare (smash_pmap_counit_natural_right_pconst B C C') ⬝ _,
    refine !phomotopy_hconcat_phconcat ⬝ idp ◾ph* _,
    refine !phomotopy_hconcat_phomotopy ◾h* idp ⬝ !phomotopy_hconcat_phconcat ⬝ idp ◾ph* _,
    refine idp ◾h* (!ppcompose_left_phomotopy_hconcat ⬝ idp ◾ph*
      (!ppcompose_left_phomotopy_hconcat ⬝ idp ◾ph* !ppcompose_left_pvconst_square)) ⬝ _,
    refine !hconcat_phomotopy_hconcat_cancel ⬝ !hconcat_phomotopy_hconcat_cancel ⬝
      !hconcat_phomotopy_hconcat_cancel ⬝ _,
    refine !phconcat_hconcat_phomotopy⁻¹ ⬝ !pvconst_square_pcompose⁻¹ ◾hp* idp
  end

  definition smash_adjoint_pmap_natural_right_pconst (A B C C' : Type*) :
    smash_adjoint_pmap_natural_right A B (pconst C C') =
    !ppcompose_left_pconst ⬝ph* !pvconst_square ⬝hp* !ppcompose_left_pconst ⬝hp*
    ppcompose_left_phomotopy !ppcompose_left_pconst :=
  begin
    refine !smash_pelim_natural_right_pconst⁻²ʰ* ⬝ _,
    refine !phomotopy_hconcat_phinverse ⬝ (!phomotopy_hconcat_phinverse ⬝
    (!hconcat_phomotopy_phinverse) ◾hp* idp ⬝ !phomotopy_hconcat_phomotopy) ◾hp* idp ⬝ _,
    refine !phomotopy_hconcat_phomotopy ⬝ idp ◾ph* ((_ ◾hp* idp) ◾hp* idp),
    apply pvconst_square_phinverse
  end

  definition smash_assoc_elim_natural_right_pconst (A B C X X' : Type*) :
    smash_assoc_elim_natural_right A B C (pconst X X') =
    !ppcompose_left_pconst ⬝ph* !pvconst_square ⬝hp* !ppcompose_left_pconst :=
  sorry


-- Π ⦃X⦄ X' g,
--     ppcompose_right
--       (pointed._trans_of_equiv_of_pequiv (smash_assoc_elim_pequiv A B C X)
--          g) ~* pmap_of_pequiv (smash_assoc_elim_pequiv A B C X') ∘* ppcompose_right
--       g

end smash


/- TO DO -/

  -- definition smash_assoc_hexagon (A B C : Type*) :
  --    smash_assoc C A B ∘* smash_comm (A ∧ B) C ∘* smash_assoc A B C ~*
  --    smash_comm A C ∧→ pid B ∘* smash_assoc A C B ∘* pid A ∧→ smash_comm B C :=
  -- sorry

  -- definition smash_assoc_triangle (A B : Type*) :
  --    smash_pbool_pequiv (A ∧ B) ∘* smash_assoc A B pbool ~* pid A ∧→ smash_pbool_pequiv B :=
  -- sorry



/- TO REMOVE -/

  definition smash_assoc' (A B C : Type*) : (A ∧ B) ∧ C ≃* A ∧ (B ∧ C) :=
  pyoneda_weak (smash_assoc_elim_pequiv A B C)
               (λX X' f g, phomotopy_of_eq (smash_assoc_elim_natural_right A B C f g))

  -- definition ppcompose_right_smash_assoc (g : A ∧ (B ∧ C) →* X) :
  --   ppcompose_right (smash_assoc_elim_pequiv A B C X g) ~*
  --   smash_assoc_elim_pequiv A B C X' ∘* ppcompose_right g :=
  -- begin

  -- end

  -- definition ppcompose_right_smash_assoc (A B C X : Type*) :
  --   ppcompose_right (smash_assoc A B C) ~* smash_assoc_elim_pequiv A B C X :=
  -- pyoneda_weak_left_inv _ _ X
