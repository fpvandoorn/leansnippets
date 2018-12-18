import .seq_colim

open eq nat sigma sigma.ops quotient equiv pi is_trunc is_equiv fiber function trunc seq_colim

universe variables v w
variables {A A' A'' : ℕ → Type} {f : seq_diagram A} {f' : seq_diagram A'} {f'' : seq_diagram A''}
          {τ τ₂ : Π⦃n⦄, A n → A' n} {p : Π⦃n⦄ (a : A n), τ (f a) = f' (τ a)}
          {p₂ : Π⦃n⦄ (a : A n), τ₂ (f a) = f' (τ₂ a)}
          {τ' : Π⦃n⦄, A' n → A'' n} {p' : Π⦃n⦄ (a' : A' n), τ' (f' a') = f'' (τ' a')}
          {P : Π⦃n⦄, A n → Type.{v}} {P' : Π⦃n⦄, A' n → Type.{w}}
          {g : seq_diagram_over f P} {g' : seq_diagram_over f' P'} {n : ℕ} {a : A n}
          (σ : Π⦃n⦄ {a : A n}, P a → P' (τ a))
          (q : Π⦃n⦄ {a : A n} (x : P a), σ (g x) =[p a] g' (σ x))

definition sigma_colim_elim_point [unfold 10] {X : Type}
  (e : Π⦃n⦄ ⦃a : A n⦄, P a → X)
  (w : Π⦃n⦄ ⦃a : A n⦄ (x : P a), e (g x) = e x)
  {n : ℕ} {a : A n} (y : seq_colim_over g (ι f a)) : X :=
begin
  induction y with k x k x,
  { exact e x },
  { exact w x }
end

-- ⊢ square
--     (apd0111 e (succ_add n (succ k)) (rep_f f (succ k) a)
--        (pathover_tro (rep_f f (succ k) a) (g x)))
--     (apd0111 e (succ_add n k) (rep_f f k a)
--        (pathover_tro (rep_f f k a) x))
--     (w x)
--     (ap e (rep_f_equiv_natural g x) ⬝ w (rep_f f k a ▸o x))

-- print apd0111_precompose
-- print ap_apd0111

-- definition apd0111_natural {A₁ A₂ A : Type} {B₁ : A₁ → Type} {B₂ : A₂ → Type}
--   {C₁ : Π⦃a⦄, B₁ a → Type} {C₂ : Π⦃a⦄, B₂ a → Type} {a a₂ : A₁}
--   {ga : A₁ → A₂} {gb : Π⦃a⦄, B₁ a → B₂ (ga a)} {gc : Π⦃a⦄ {b : B₁ a}, C₁ b → C₂ (gb b)}
--   {b : B₁ a} {b₂ : B₁ a₂} {c : C₁ b} {c₂ : C₁ b₂}
--   (f₁ : Π⦃a⦄ {b : B₁ a}, C₁ b → A) (f₂ : Π⦃a⦄ {b : B₂ a}, C₂ b → A) (Ha : a = a₂) (Hb : b =[Ha] b₂)
--     (Hc : c =[apd011 C₁ Ha Hb] c₂)
--   (h : Π⦃a⦄ {b : B₁ a} (c : C₁ b), f₁ c = f₂ (gc c)) :
--   square (apd0111 f₁ Ha Hb Hc) (apd0111 f₂ (ap ga Ha) (pathover_ap B₂ ga (apo gb Hb)) _)
--     (h c) (h (transporto C₁ _ c₂)) :=
-- begin end

definition sigma_colim_elim_path {X : Type}
  (e : Π⦃n⦄ ⦃a : A n⦄, P a → X)
  (w : Π⦃n⦄ ⦃a : A n⦄ (x : P a), e (g x) = e x)
  {n : ℕ} (a : A n) :
    pathover (λx, seq_colim_over g x → X) (sigma_colim_elim_point e w)
      (glue f a) (sigma_colim_elim_point e w) :=
begin
  apply arrow_pathover_constant_right, intro y,
  refine _ ⬝ ap (sigma_colim_elim_point e w) (seq_colim_over_glue g _)⁻¹ᵖ,
  induction y with k x k x,
  { exact apd0111 e _ (rep_f f k a) !pathover_tro },
  { apply eq_pathover,
    refine !elim_glue ⬝ph _ ⬝hp (ap_compose (sigma_colim_elim_point e w ∘ shift_down _) _ _ ⬝
      ap02 _ !elim_glue ⬝ !ap_con ⬝
      !ap_compose⁻¹ ◾ (!ap_compose ⬝ ap02 _ !elim_glue ⬝ !elim_glue))⁻¹,
    esimp [function.compose],
    apply move_right_of_top, exact sorry
  }
end

definition sigma_colim_elim {X : Type} (e : Π⦃n⦄ ⦃a : A n⦄, P a → X)
  (w : Π⦃n⦄ ⦃a : A n⦄ (x : P a), e (g x) = e x) (v : Σ(x : seq_colim f), seq_colim_over g x) : X :=
begin
  induction v with x y,
  induction x with n a n a,
  { exact sigma_colim_elim_point e w y },
  { exact sigma_colim_elim_path e w a }
end

theorem sigma_colim_elim_glue {X : Type} (e : Π⦃n⦄ ⦃a : A n⦄, P a → X)
  (w : Π⦃n⦄ ⦃a : A n⦄ (x : P a), e (g x) = e x) {n : ℕ} {a : A n} (x : P a) :
    ap (sigma_colim_elim e w) (glue' g x) = w x :=
begin
  refine !ap_dpair_eq_dpair ⬝ _,
  refine !apd011_eq_apo11_apd ⬝ _,
  refine ap (λx, apo11_constant_right x _) !rec_glue ⬝ _,
  refine !apo11_arrow_pathover_constant_right ⬝ _,
  refine whisker_right _ !idp_con ⬝ _,
  rewrite [▸*, tr_eq_of_pathover_concato_eq, ap_con, ↑glue_over,
           to_right_inv !pathover_equiv_tr_eq, ap_inv, inv_con_cancel_left],
  apply elim_glue
end

example {E : (Σ(x : seq_colim f), seq_colim_over g x) → Type}
  (e : Π⦃n⦄ ⦃a : A n⦄ (x : P a), E ⟨ι f a, ιo g x⟩)
  (w : Π⦃n⦄ ⦃a : A n⦄ (x : P a), pathover E (e (g x)) (glue' g x) (e x))
  {n : ℕ} {a : A n} (x : P a) : sigma_colim_rec g e w ⟨ι f a, ιo g x⟩ = e x :=
by reflexivity


include q


definition seq_colim_over_functor_point (a : A n) :
  seq_colim_over g (ι f a) → seq_colim_over g' (ι f' (τ a)) :=
begin
  refine seq_colim_functor _ _,
  { intro k x, exact transport (@P' (n+k)) (rep_natural τ p k a) (σ x) },
  { intro k x,
    refine _ ⬝ (fn_tr_eq_tr_fn (rep_natural τ p k a) (@g' _) (σ x))⁻¹,
    refine _ ⬝ tr_ap (@P' _) (@f' _) _ _,
    refine _ ⬝ ap (transport _ _) (tr_eq_of_pathover (q x)),
    exact con_tr (p _) (ap _ (rep_natural τ p k _)) (σ (g x)) }
end

definition seq_colim_over_functor ⦃a : seq_colim f⦄ :
  seq_colim_over g a → seq_colim_over g' (seq_colim_functor τ p a) :=
begin
  induction a,
  { exact seq_colim_over_functor_point σ q a },
  { apply arrow_pathover_left, esimp, intro x,
    induction x with k x k x,
    { exact sorry },
    { exact sorry }}
end

definition sigma_colim_of_colim_sigma_natural (a : seq_colim (seq_diagram_sigma g)) :
  hsquare (sigma_colim_of_colim_sigma g) (sigma_colim_of_colim_sigma g')
    (seq_colim_functor (λn, sigma_functor (@τ n) (@σ n)) (λn, sigma_functor_hsquare (@p n) (@q n)))
          (sigma_functor (seq_colim_functor τ p) (seq_colim_over_functor σ q)) :=
begin
  exact sorry
end
