import homotopy.circle

open eq bool equiv circle sigma pi

namespace bool

  -- definition elim2_type_seg1_pathover (Pb1 Pb2 : Type) (Ps1 Ps2 : Pb1 ≃ Pb2) (x : Pb1) :
  --   pathover (elim2_type Pb1 Pb2 Ps1 Ps2) x seg1 (Ps1 x) :=
  -- pathover_of_tr_eq (apd10 (elim2_type_seg1 Pb1 Pb2 Ps1 Ps2) x)

  -- definition elim2_type_seg2_pathover (Pb1 Pb2 : Type) (Ps1 Ps2 : Pb1 ≃ Pb2) (x : Pb1) :
  --   pathover (elim2_type Pb1 Pb2 Ps1 Ps2) x seg2 (Ps2 x) :=
  -- pathover_of_tr_eq (apd10 (elim2_type_seg2 Pb1 Pb2 Ps1 Ps2) x)

  definition pathover_tr_pathover_idp_of_eq2 {A : Type} {B : A → Type} {a a' : A} {b : B a} {b' : B a'}
    {p : a = a'} (q : p ▸ b = b') :
    pathover_tr p b ⬝o pathover_idp_of_eq q = pathover_of_tr_eq q :=
  begin induction q; induction p; reflexivity end

  definition tr_eq_of_pathover_pathover_tr {A : Type} {B : A → Type} {a a₂ : A} (p : a = a₂)
    (b : B a) : tr_eq_of_pathover (pathover_tr p b) = idp :=
  by induction p; reflexivity









  definition M [unfold 1] : S¹ → Type₀ :=
  circle.elim_type bool equiv_bnot

  definition circle_of_M [unfold 1] (x : Σx, M x) : S¹ :=
  begin
    induction x with x m,
    induction x,
    { exact cond m base2 base1 /- tt ↦ base2, ff ↦ base1 -/ },
    { apply arrow_pathover_constant_right, intro b,
      refine _ ⬝ (ap (λx, cond x _ _) (elim_type_loop _ _ b))⁻¹,
      induction b, exact seg2, exact seg1⁻¹
      }
  end

  definition M_of_circle [unfold 1] (x : S¹) : Σx, M x :=
  begin
    induction x using circle.elim2,
    { exact ⟨base, ff⟩ },
    { exact ⟨base, tt⟩ },
    { exact (dpair_eq_dpair loop (elim_type_loop_pathover _ _ tt))⁻¹ },
    { exact dpair_eq_dpair loop (elim_type_loop_pathover _ _ ff) },
  end

  definition M_of_circle_of_M_base [unfold 1] (b : M base) : M_of_circle (circle_of_M ⟨base, b⟩) = ⟨base, b⟩ :=
  by induction b; reflexivity; reflexivity

  definition circle_equiv_M : S¹ ≃ Σx, M x :=
  equiv.MK M_of_circle circle_of_M
    begin
      intro x, induction x with x m,
      induction x,
      { exact M_of_circle_of_M_base m },
      { apply pi_pathover_left, intro b,
        apply eq_pathover_id_right,
        refine ap_compose M_of_circle _ _ ⬝
          ap02 _ (!ap_dpair_eq_dpair ⬝ !apd011_eq_apo11_apd ⬝
            ap (λx, apo11_constant_right x _) !rec_loop ⬝ !apo11_arrow_pathover_constant_right) ⬝ph _,
        esimp,
        refine !ap_con ⬝ (!ap_con ⬝ idp ◾ (!ap_inv ⬝ !ap_compose'⁻²))
          ◾ (!ap_compose' ⬝ ap02 _ !tr_eq_of_pathover_pathover_tr) ⬝ph _,
        note sq := (natural_square M_of_circle_of_M_base (elim_type_loop _ _ b))⁻¹ᵛ,
        esimp at sq, esimp,
        refine (_ ⬝v sq) ⬝hp !con_inv_cancel_right, clear sq,
        induction b,
        { apply hdeg_square, refine !elim2_seg2 ⬝ _⁻¹,
          refine idp ◾ !ap_dpair ⬝ !dpair_eq_dpair_con⁻¹ ⬝ ap (dpair_eq_dpair loop) _,
          rexact pathover_tr_pathover_idp_of_eq2 (elim_type_loop bool equiv_bnot ff) },
        { apply hdeg_square, refine !ap_inv ⬝ !elim2_seg1⁻² ⬝ !inv_inv ⬝ _⁻¹,
          refine idp ◾ !ap_dpair ⬝ !dpair_eq_dpair_con⁻¹ ⬝ ap (dpair_eq_dpair loop) _,
          rexact pathover_tr_pathover_idp_of_eq2 (elim_type_loop bool equiv_bnot tt) }}
    end
    begin
      intro x, induction x using circle.rec2,
      { reflexivity },
      { reflexivity },
      { apply eq_pathover_id_right, apply hdeg_square, refine ap_compose circle_of_M _ _ ⬝ _,
        refine ap02 _ !elim2_seg1 ⬝ !ap_inv ⬝ _⁻² ⬝ !inv_inv,
        refine !ap_dpair_eq_dpair ⬝ !apd011_eq_apo11_apd ⬝ ap (λx, apo11_constant_right x _) !rec_loop ⬝
          !apo11_arrow_pathover_constant_right ⬝ _,
        esimp,
        refine idp ◾ idp ◾ ap02 _ _ ⬝ !inv_con_cancel_right,
        exact to_right_inv (pathover_equiv_tr_eq _ _ _) _ },
      { apply eq_pathover_id_right, apply hdeg_square, refine ap_compose circle_of_M _ _ ⬝ _,
        refine ap02 _ !elim2_seg2 ⬝ _,
        refine !ap_dpair_eq_dpair ⬝ !apd011_eq_apo11_apd ⬝
            ap (λx, apo11_constant_right x _) !rec_loop ⬝ !apo11_arrow_pathover_constant_right ⬝ _,
        esimp,
        refine idp ◾ idp ◾ ap02 _ _ ⬝ !inv_con_cancel_right, exact to_right_inv (pathover_equiv_tr_eq _ _ _) _ }
    end

end bool
