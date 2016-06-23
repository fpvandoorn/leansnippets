import homotopy.circle
open circle eq int nat prod sum equiv function is_trunc

/---------------------------------------------------------------------------------------------------
We use the Licata trick to define
HIT X :=
| b : X
| s : (S¹ → X) → X
| p : b = b
--------
this is a W-suspension X with
A = bool
B ff = empty
B tt = S¹
one equality: sup ff _ = sup ff _
--------
Note: we don't (and can't in Lean) actually hide the recursor for the "wrong" datatype X,
  so we have to be careful not to use X.rec or induction x for (x : X)
---------------------------------------------------------------------------------------------------/
namespace hide
  inductive X :=
  | b : X
  | s : (S¹ → X) → X
  open X
  axiom p : b = b

  definition rec [unfold 5] {P : X → Type} (Pb : P b) (Ps : Π(f : S¹ → X), (Π(x : S¹), P (f x)) →  P (s f))
    (Pp : Pb =[p] Pb) (x : X) : P x :=
  X.rec_on x Pb Ps

  axiom rec_p {P : X → Type} (Pb : P b) (Ps : Π(f : S¹ → X), (Π(x : S¹), P (f x)) →  P (s f))
    (Pp : Pb =[p] Pb) : apd (rec Pb Ps Pp) p = Pp

  definition elim [unfold 5] {P : Type} (Pb : P) (Ps : Π(f : S¹ → X), (S¹ → P) →  P)
    (Pp : Pb = Pb) (x : X) : P :=
  rec Pb Ps (pathover_of_eq _ Pp) x

  theorem elim_p {P : Type} (Pb : P) (Ps : Π(f : S¹ → X), (S¹ → P) →  P)
    (Pp : Pb = Pb) : ap (elim Pb Ps Pp) p = Pp := sorry -- easy to prove

  -- abbreviation Y := ℕ × S¹ ⊎ ℕ × ℤ × ℕ
  inductive Ztree :=
  | leaf : Ztree
  | node : ℤ → Ztree → Ztree
  abbreviation W := Ztree × S¹

/-
  need:
  (S¹ → Y) ≃ (Σ(y : Y), y = y)
  (Σ(y : X + Y), y = y) ≃ (Σ(x : X), x = x) + (Σ(y : Y), y = y)
  (Σ(x : X), x = x) ≃ X if x is set
  (Σ(y : X × Y), y = y) ≃ (Σ(x : X), x = x) × (Σ(y : Y), y = y) ?
  (Σ(y : S¹), y = y) ≃ S¹ × ℤ?
-/

--   definition φ (x : X) : Y :=
--   begin
--     refine (elim _ _ _ x),
--     { exact inl (0, base)},
--     { intros f g,
-- /-
--   g is constant (inl (n, x)) ↦ inl (n+1, x)
--   g is constant (inr (n, m, k)) ↦ inr (n, m, k+1)
--   g base = inl (n, x) and ap f loop = 'loop'ᵐ ↦ (n, m, 0)
-- -/ },
--     { exact ap inl (prod_eq idp loop)},
--   end

  -- definition ψ₁ (n : ℕ) : X :=
  -- begin
  --   induction n with n x,
  --     exact b,
  --     exact s (λz, x)
  -- end

  -- definition pψ (n : ℕ) : ψ₁ n = ψ₁ n :=
  -- begin
  --   induction n with n q,
  --     exact p,
  --     exact ap (λx, s (λz, x)) q,
  -- end

  definition px (x : X) : x = x :=
  begin
    refine rec _ _ _ x,
    { exact p},
    { intro f q, exact ap s (eq_of_homotopy q)},
    { apply eq_pathover, rewrite +ap_id, exact square_of_eq idp}
  end

  -- definition ψY (y : Y) : X :=
  -- begin
  --   induction y with y y,
  --   { induction y with n z, induction z,
  --     { exact ψ₁ n},
  --     { exact pψ n}},
  --   { induction y with n y, induction y with m k,
  --     induction k with k x,
  --     { apply s, intro z, induction z, exact ψ₁ n, apply pψ},
  --     { apply s, intro z, exact x}}
  -- end

  section
  open equiv sigma sigma.ops
  definition foo (A : Type) : (S¹ → A) ≃ Σ(a : A), a = a :=
  begin
    fapply equiv.MK,
    { intro f, exact ⟨f base, ap f loop⟩},
    { intro q z, induction z, exact q.1, exact q.2},
    { intro q, fapply sigma_eq, reflexivity, esimp, apply pathover_idp_of_eq, apply elim_loop},
    { intro f, esimp, /-not fully simplified-/ apply eq_of_homotopy, intro z, esimp, induction z,
        reflexivity,
        esimp, apply eq_pathover, apply hdeg_square, esimp, apply elim_loop},
  end
  end

  definition ψ (w : W) : X :=
  begin
    induction w with w z, induction w with n zz x,
    { induction z,
        exact b,
        exact p},
    { induction z,
      { apply s, intro z, induction z,
        { exact x},
        { apply power !px n}},
      { apply px}}
  end

  definition φ (x : X) : W :=
  begin
    refine (elim _ _ _ x),
    { exact (Ztree.leaf, base)},
    { intros f g, clear f, constructor,
      { apply Ztree.node,
        { apply to_fun (eq_equiv_Z (pr2 (g base))), apply ap (pr2 ∘ g) loop},
        { exact pr1 (g base)}},
      { exact pr2 (g base)}},
    { exact prod_eq idp loop},
  end

  definition ψnode (zz : Ztree) (n : ℤ)
    : ψ (Ztree.node n zz, base) = s (circle.elim (ψ (zz, base)) (power (px (ψ (zz, base))) n)) :=
  idp

  definition φs (f : S¹ → X)
    : φ (s f) = (Ztree.node (to_fun (eq_equiv_Z (pr2 (φ (f base)))) (ap (pr2 ∘ φ ∘ f) loop))
                           (pr1 (φ (f base))), pr2 (φ (f base))) :=
  idp

  definition ψφ (x : X) : ψ (φ x) = x :=
  begin
    refine (rec _ _ _ x),
    { reflexivity},
    { intros f q, rewrite [↑[φ]/-,↓φ (f base) FAILS-/], apply sorry},
    { apply eq_pathover, apply hdeg_square, rewrite [ap_id, ap_compose ψ φ,↑φ,elim_p],
      apply sorry}
  end

--  definition bar {A B : Type} {P : A → Type} (f : Π{a}, P a → B) {a a' : A} (p : a = a') : f

  definition φψ (w : W) : φ (ψ w) = w :=
  begin
    induction w with w z, induction w with n zz q,
    { esimp [ψ], induction z,
      { reflexivity},
      { apply eq_pathover, apply hdeg_square, rewrite [ap_compose φ,elim_loop,↑φ,elim_p]}},
    { induction z,
      { rewrite [ψnode,φs], apply prod_eq,
        { esimp, apply ap011 Ztree.node,
          { exact sorry},
            rewrite q},
        { esimp, rewrite q}},
      { exact sorry}}
  end
end hide

/---------------------------------------------------------------------------------------------------
Question:
Is
HIT ntree :=
| leaf : ntree
| node : (ℕ → ntree) → ntree
| nirr : Π(f : ℕ ≃ ℕ) (g : ℕ → ntree), node (g ∘ f) = node g
| tru  : is_set ntree
the set-truncation of
HIT tree :=
| leaf : tree
| node : (ℕ → tree) → tree
| irr  : Π(f : ℕ ≃ ℕ) (g : ℕ → tree), node (g ∘ f) = node g
---------------------------------------------------------------------------------------------------/

namespace hide2

  inductive ntree :=
  | leaf : ntree
  | node : (ℕ → ntree) → ntree
  open ntree

  constant nirr : Π(f : ℕ ≃ ℕ) (g : ℕ → ntree), node (g ∘ f) = node g
  constant tru : is_set ntree



end hide2
