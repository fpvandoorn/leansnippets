import hit.quotient types.W hit.trunc function

open eq quotient Wtype sigma equiv equiv.ops function is_equiv pi

namespace W_colim

  section
  parameters (A : Type) (B : A → Type) (P : (W a, B a) → Type)
             (g : Π⦃a : A⦄ {b : B a} {f : B a → W a, B a}, P (f b) → P (sup a f))
  variables  {a : A} (b : B a) {f : B a → W a, B a} {w : W a, B a} (p : P w) (q : P (f b))

  inductive W_rel : sigma P → sigma P → Type :=
  | Rmk : Π{a : A} {b : B a} (f : B a → W a, B a) (q : P (f b)),
          W_rel ⟨f b, q⟩ ⟨sup a f, g q⟩

  definition W_colim : Type := quotient W_rel

  parameters {A B}
  variable (w)
  definition inclusion : W_colim :=
  class_of W_rel ⟨w, p⟩

  parameters {P g}
  variable {w}
  abbreviation wι := inclusion w

  definition glue : wι q = wι (g q) :=
  eq_of_rel W_rel (W_rel.Rmk f q)

  protected definition rec {Q : W_colim → Type} (Qincl : Π⦃w : W a, B a⦄ (p : P w), Q (wι p))
    (Qglue : Π⦃a : A⦄ (b : B a) {f : B a → W a, B a} (q : P (f b)),
      Qincl q =[glue b q] Qincl (g q)) (aa : W_colim) : Q aa :=
  begin
    induction aa with v v v' r,
    { induction v with w p, exact Qincl p},
    { induction r, apply Qglue}
  end

  protected definition rec_on [reducible] {Q : W_colim → Type} (aa : W_colim)
    (Qincl : Π⦃w : W a, B a⦄ (p : P w), Q (wι p))
    (Qglue : Π⦃a : A⦄ (b : B a) {f : B a → W a, B a} (q : P (f b)),
      Qincl q =[glue b q] Qincl (g q)) : Q aa :=
  rec Qincl Qglue aa

  theorem rec_glue {Q : W_colim → Type} (Qincl : Π⦃w : W a, B a⦄ (p : P w), Q (wι p))
    (Qglue : Π⦃a : A⦄ (b : B a) {f : B a → W a, B a} (q : P (f b)),
      Qincl q =[glue b q] Qincl (g q))
    {a : A} (b : B a) {f : B a → W a, B a} (q : P (f b)) :
    apdo (rec Qincl Qglue) (glue b q) = Qglue b q :=
  !rec_eq_of_rel

  protected definition elim {Q : Type} (Qincl : Π⦃w : W a, B a⦄ (p : P w), Q)
    (Qglue : Π⦃a : A⦄ (b : B a) {f : B a → W a, B a} (q : P (f b)),
      Qincl q = Qincl (g q)) : W_colim → Q :=
  rec Qincl (λa b f q, pathover_of_eq (Qglue b q))

  protected definition elim_on [reducible] {Q : Type} (aa : W_colim)
    (Qincl : Π⦃w : W a, B a⦄ (p : P w), Q)
    (Qglue : Π⦃a : A⦄ (b : B a) {f : B a → W a, B a} (q : P (f b)),
      Qincl q = Qincl (g q)) : Q :=
  elim Qincl Qglue aa

  theorem elim_glue {Q : Type} (Qincl : Π⦃w : W a, B a⦄ (p : P w), Q)
    (Qglue : Π⦃a : A⦄ (b : B a) {f : B a → W a, B a} (q : P (f b)),
      Qincl q = Qincl (g q))
    {a : A} (b : B a) {f : B a → W a, B a} (q : P (f b))
      : ap (elim Qincl Qglue) (glue b q) = Qglue b q :=
  begin
    apply eq_of_fn_eq_fn_inv !(pathover_constant (glue b q)),
    rewrite [▸*,-apdo_eq_pathover_of_eq_ap,↑elim,rec_glue],
  end

  protected definition elim_type (Qincl : Π⦃w : W a, B a⦄ (p : P w), Type)
    (Qglue : Π⦃a : A⦄ (b : B a) {f : B a → W a, B a} (q : P (f b)),
      Qincl q ≃ Qincl (g q)) : W_colim → Type :=
  elim Qincl (λa b f q, ua (Qglue b q))

  protected definition elim_type_on [reducible] (aa : W_colim)
    (Qincl : Π⦃w : W a, B a⦄ (p : P w), Type)
    (Qglue : Π⦃a : A⦄ (b : B a) {f : B a → W a, B a} (q : P (f b)),
      Qincl q ≃ Qincl (g q)) : Type :=
  elim_type Qincl Qglue aa

  theorem elim_type_glue (Qincl : Π⦃w : W a, B a⦄ (p : P w), Type)
    (Qglue : Π⦃a : A⦄ (b : B a) {f : B a → W a, B a} (q : P (f b)),
      Qincl q ≃ Qincl (g q))
    {a : A} (b : B a) {f : B a → W a, B a} (q : P (f b))
      : transport (elim_type Qincl Qglue) (glue b q) = Qglue b q :=
  by rewrite [tr_eq_cast_ap_fn,↑elim_type,elim_glue];apply cast_ua_fn

  end

end W_colim

attribute W_colim.rec W_colim.elim [unfold 8] [recursor 8]
attribute W_colim.elim_type [unfold 7]
attribute W_colim.rec_on W_colim.elim_on [unfold 6]
attribute W_colim.elim_type_on [unfold 5]
attribute W_colim.inclusion W_colim.wι [constructor]

open W_colim

namespace Wtype

  section

  open sigma pi eq is_trunc trunc sigma.ops function
  universe variables u v
  variables {A : Type.{u}} {B : A → Type.{v}}

  inductive le : (W a, B a) → (W a, B a) → Type.{max u v} :=
  | refl : Πw, le w w
  | step : Π{w a f b}, le w (f b) → le w (sup a f)

  infix ` ≤ ` := le

  definition down (w : W a, B a) : Type.{max u v} := Σv, ∥ v ≤ w ∥
  prefix `↓↓`:(max+1) := down
  definition to_tree [unfold 4] {w : W a, B a} (x : ↓↓w) : W a, B a := x.1
  definition to_rel [unfold 4] {w : W a, B a} (x : ↓↓w) : ∥ to_tree x ≤ w ∥ := x.2

  definition down_functor [constructor] {a : A} (b : B a) (f : B a → W a, B a) (x : ↓↓(f b))
    : ↓↓(sup a f) :=
  begin
    fapply sigma.mk,
    { exact to_tree x},
    { refine trunc.rec _ (to_rel x), intro H, exact tr (le.step H)}
  end

  variable (B)
  definition colim_down [reducible] := W_colim A B down (@down_functor A B)

  variable {B}
  definition of_W [constructor] (w : W a, B a) : colim_down B := wι ⟨w, tr !le.refl⟩

  definition of_W_eq {v w : W a, B a} (H : v ≤ w) : of_W v = wι ⟨v, tr H⟩ :=
  begin
    induction H with v v a f b H IH,
    { reflexivity},
    { refine IH ⬝ !glue}
  end

  definition tr_of_W_eq {v w : W a, B a} (H : ∥ v ≤ w ∥) : ∥ of_W v = wι ⟨v, H⟩ ∥ :=
  begin
    refine trunc.rec _ H, clear H,
    intro H, apply tr, apply of_W_eq H
  end

  definition to_W [unfold 3] (w : colim_down B) : W a, B a :=
  begin
    induction w,
    { exact to_tree p},
    { reflexivity},
  end

  definition of_W_to_W (w : colim_down B) : ∥ of_W (to_W w) = w ∥ :=
  begin
    induction w,
    { induction p with v H, esimp, exact tr_of_W_eq H},
    { apply is_hprop.elimo}
  end

  definition to_W_of_W (w : W a, B a) : to_W (of_W w) = w :=
  idp

  definition W_equiv_colim_down_of_is_hset [H : is_hset (W a, B a)]
    : (W a, B a) ≃ trunc 0 (colim_down B) :=
  begin

    fapply equiv.MK,
    { exact tr ∘ of_W},
    { exact trunc.rec to_W},
    { refine trunc.rec _, intro w, esimp,
      induction w,
      { induction p with v H2, esimp, refine trunc.rec _ H2, exact λH3, ap tr !of_W_eq},
      { apply is_hprop.elimo}},
    { intro w, reflexivity}
  end


  /-
    if W a, B a is a set, then we can conclude from this that (W a, B a) ≃ trunc 0 (colim_down B)
    (this takes a little bit of work)
  -/

  -- variable (B)
  -- definition W_equiv_colim_down : (W a, B a) ≃ colim_down B :=
  -- begin
  --   fapply equiv.MK,
  --   { exact of_W},
  --   { exact to_W},
  --   { intro w, induction w,
  --     { induction p with v H, esimp, },
  --     { }},
  --   { }
  -- end

  end

  section

  variables {A A' : Type} {B : A → Type} {B' : A' → Type} (g : A → A') (h : Πa, B' (g a) → B a)

  definition W_functor : (W a, B a) → W a', B' a' :=
  Wtype.rec (λa f IH, sup (g a) (λb', IH (h _ b')))

  definition id2 [unfold_full] ⦃a : A⦄ : B a → B a := id
  variables (B B')
  definition W_functor_id : (W a, B' (g a)) → W a', B' a' :=
  Wtype.rec (λa f IH, sup (g a) (λb', IH b'))

  definition θ : (W a, B a) → W X, X :=
  W_functor_id id B

  variables {B' g}
  definition is_injective_ap_W_functor [H : is_embedding g] {w w' : W a, B' (g a)}
    (p : W_functor_id B' g w = W_functor_id B' g w') : w = w' :=
  begin
    revert w' p, induction w with a f IH, intro w', induction w' with a' f' IH', clear IH',
    esimp at *, intro p, fapply Wtype_eq,
    { exact (ap g)⁻¹ (Wtype_eq_pr1 p)},
    { esimp, apply arrow_pathover_constant_right, intro b,
      rewrite [↑W_functor_id at p],
      refine IH _ _ (apo10_constant_right (Wtype_eq_pr2 p) b) ⬝ _,
      apply ap f',
      refine _ ⬝ (tr_compose B' _ _ _)⁻¹,
      refine ap010 (transport B') _ b,
      symmetry, apply right_inv}
  end

  variables (B g)
  definition is_embedding_W_functor [H : is_embedding g] : is_embedding (W_functor_id B' g) :=
  begin
    intro w w',
    fapply adjointify,
    { exact is_injective_ap_W_functor},
    { exact sorry},
    { intro p, induction p, induction w with a f IH,
      change sup_eq_sup ((ap g)⁻¹ idp)
       (arrow_pathover_constant_right (λ (b : B' (g a)),
          @is_injective_ap_W_functor _ _ _ _ H _ _ idp ⬝ ap f
            (ap010 (transport B') (right_inv (ap g) idp)⁻¹ b ⬝ (tr_compose B' g
                ((ap g)⁻¹ idp)
                b)⁻¹))) = refl (sup a f),
      exact sorry
      }
  end

  end


  exit

  section
  parameters {A : Type} (B : A → Type) (R : A → A → Type)

  inductive Wsusp_rel {a : A} (Pf : B a → Type) : (Πb, Pf b) → (Πb, Pf b) → Type :=
  | Rmk : Π{a' : A} (r : R a a') (l : B a → (Πb, Pf b)) (r : B a' → (Πb, Pf b)),
          Wsusp_rel Pf _ _

  definition P (w : W a, B a) : Type :=
  begin
    induction w with a f Pf,
    exact @quotient (Πb, Pf b) _
  end

  definition Wsusp : Type := W_colim A B P _

  end

end Wtype


-- namespace Wsusp

--   section
--   parameters {A : Type} (B : A → Type) (R : A → A → Type)

--   inductive Wsusp_rel {a : A} (Pf : B a → Type) : (Πb, Pf b) → (Πb, Pf b) → Type :=
--   | Rmk : Π{a' : A} (r : R a a') (l : B a → (Πb, Pf b)) (r : B a' → (Πb, Pf b)),
--           Wsusp_rel Pf _ _

--   definition P (w : W a, B a) : Type :=
--   begin
--     induction w with a f Pf,
--     exact @quotient (Πb, Pf b) _
--   end

--   definition Wsusp : Type := W_colim A B P _

--   end

-- end Wsusp
