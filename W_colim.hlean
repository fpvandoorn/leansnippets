import hit.quotient types.W hit.trunc function

open eq quotient Wtype sigma equiv equiv.ops function is_equiv pi sum unit function

namespace W_colim

  section
  parameters (A : Type) (B : A → Type) (P : (W a, B a) → Type)
             (g : Π⦃a : A⦄ {b : B a} {f : B a → W a, B a}, P (f b) → P (sup a f))
  variables  {a : A} (b : B a) {f : B a → W a, B a} {w : W a, B a} (p : P w) (q : P (f b))

  inductive W_rel : sigma P → sigma P → Type :=
  | Rmk : Π{a : A} {b : B a} (f : B a → W a, B a) (q : P (f b)),
          W_rel ⟨f b, q⟩ ⟨sup a f, g q⟩

  parameters {A B}
  definition W_colim : Type := quotient W_rel

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

  definition down (w : W a, B a) : Type.{max u v} := Σv, v ≤ w
  prefix `↓↓`:(max+1) := down
  definition to_tree [unfold 4] {w : W a, B a} (x : ↓↓w) : W a, B a := x.1
  definition to_rel [unfold 4] {w : W a, B a} (x : ↓↓w) : to_tree x ≤ w := x.2

  definition down_functor [constructor] {a : A} (b : B a) (f : B a → W a, B a) (x : ↓↓(f b))
    : ↓↓(sup a f) :=
  begin
    fapply sigma.mk,
    { exact to_tree x},
    { exact le.step (to_rel x)}
  end

  /- begin intermezzo -/
  definition down' : (W a, B a) → Type.{max u v} :=
  Wtype.rec (λa f downs, unit + Σb, downs b)

  definition self [unfold 3] (w : W a, B a) : down' w :=
  by induction w; exact inl star

  definition down'_of_down {w : W a, B a} (x : ↓↓w) : down' w :=
  begin
    induction x with v H, induction H with w w a f b H IH,
    { apply self},
    { esimp [down'], exact inr ⟨b, IH⟩}
  end

  definition down_of_down' {w : W a, B a} (x : down' w) : ↓↓w :=
  begin
    induction w with a f IH, esimp [down'] at x,
    induction x with x x,
    { exact ⟨sup a f, !le.refl⟩},
    { induction x with b x, refine down_functor b f _, apply IH, exact x}
  end

  definition down_equiv [constructor] (w : W a, B a) : ↓↓w ≃ down' w :=
  begin
    fapply equiv.MK,
    { exact down'_of_down},
    { exact down_of_down'},
    { intro x, induction w with a f IH, esimp [down'] at x,
      induction x with x x: esimp,
      { unfold [down_of_down',down'_of_down], induction x, reflexivity},
      { induction x with b x,
        rewrite [▸*, ↑down_of_down', ↓@down_of_down' A B, ↑down'_of_down],
        apply ap inr, apply ap (sigma.mk b), refine _ ⬝ IH b x,
        apply ap down'_of_down !sigma.eta}},
    { intro x, induction x with v H, induction H with w w a f b H IH,
      { unfold [down'_of_down], cases w, reflexivity},
      { exact ap (down_functor b f) IH}}
  end
  /- end intermezzo -/

  variable (B)
  definition colim_down [reducible] := W_colim down (@down_functor A B)

  variable {B}
  definition of_W [constructor] (w : W a, B a) : colim_down B := wι ⟨w, !le.refl⟩

  definition of_W_eq {v w : W a, B a} (H : v ≤ w) : of_W v = wι ⟨v, H⟩ :=
  begin
    induction H with v v a f b H IH,
    { reflexivity},
    { refine IH ⬝ !glue}
  end

  -- definition of_W_eq {v w : W a, B a} (H : v ≤ w) : of_W v = wι ⟨v, H⟩ :=
  -- begin
  --   induction H with v v a f b H IH,
  --   { reflexivity},
  --   { refine IH ⬝ !glue}
  -- end

  -- definition tr_of_W_eq {v w : W a, B a} (H : ∥ v ≤ w ∥) : ∥ of_W v = wι ⟨v, H⟩ ∥ :=
  -- begin
  --   refine trunc.rec _ H, clear H,
  --   intro H, apply tr, apply of_W_eq H
  -- end

  definition to_W [unfold 3] (w : colim_down B) : W a, B a :=
  begin
    induction w,
    { exact to_tree p},
    { reflexivity},
  end

  definition of_W_to_W (w : colim_down B) : of_W (to_W w) = w :=
  begin
    induction w,
    { induction p with v H, esimp, exact of_W_eq H},
    { apply eq_pathover, induction q with v H,
      rewrite [ap_id, ap_compose of_W to_W, ↑to_W],
      refine ap (ap of_W) !elim_glue ⬝ph _,
      apply square_of_eq, rewrite [▸*, idp_con]
      }
  end

  definition to_W_of_W (w : W a, B a) : to_W (of_W w) = w :=
  idp

  definition W_equiv_colim_down [constructor] : (W a, B a) ≃ colim_down B :=
  begin
    fapply equiv.MK,
    { exact of_W},
    { exact to_W},
    { exact of_W_to_W},
    { intro w, reflexivity}
  end

  end

end Wtype


namespace Wtype

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

end Wtype

namespace Wcompact

  variables {A : Type} {B : A → Type} (P : (W a, B a) → Type)
            (g : Π⦃a : A⦄ {b : B a} {f : B a → W a, B a}, P (f b) → P (sup a f))

  variables {w : W a, B a} (p : P w)

  definition arrow_obj (X : Type) (w : W a, B a) : Type := X → P w

  definition arrow_mor {X : Type} ⦃a : A⦄ {b : B a} {f : B a → W a, B a} (p : arrow_obj P X (f b))
    : arrow_obj P X (sup a f) :=
  λx, g (p x)

  definition arrow_colim_of_colim_arrow {X : Type} (h : W_colim (arrow_obj P X) (arrow_mor P g))
    (x : X) : W_colim P g :=
  begin induction h with w h a b f h, exact wι (h x), exact glue b (h x) end

  definition W_compact [class] (X : Type) {A : Type} (B : A → Type) : Type :=
  Π(P : (W a, B a) → Type)
   (g : Π⦃a : A⦄ {b : B a} {f : B a → W a, B a}, P (f b) → P (sup a f)),
   is_equiv (arrow_colim_of_colim_arrow P g
     : W_colim (arrow_obj P X) (arrow_mor P g) → (X → W_colim P g))

  -- is this true?
exit
  definition W_compact_self {A : Type} (B : A → Type) (a : A) : W_compact (B a) B :=
  begin
    intro P g,
    fapply adjointify,
    { intro h, refine !@wι _,
      { apply sup a, intro b, refine W_colim.elim _ _ (h b),
        { intro w p, exact w},
        { intro a b f p, }},
      { }},
    { },
    { },
  end

end Wcompact

exit -- below doesn't work well yet

open Wtype sigma.ops
namespace Wsusp

  section
  universe variables u v w
  parameters {A : Type.{u}} (B : A → Type.{v}) (R : A → A → Type.{w})

  inductive rel2.{z} {a : A} (X : B a → Type.{z}) (f : Πb, X b → A)
    : (unit + Σ (b : B a), X b) → (unit + Σ (b : B a), X b) → Type.{max v w z} :=
  | Rmk : Π(b : B a) (x : X b) (r : R a ((f b x))), rel2 X f (inl star) (inr ⟨b, x⟩)

  inductive Wsusp_rel (w : W a, B a) : ↓↓w → ↓↓w → Type :=
  | Rmk : Π{a a' : A} {f : B a → W a, B a} {f' : B a' → W a, B a}
          (H : sup a f ≤ w) (H' : sup a' f' ≤ w),
          Wsusp_rel w ⟨sup a f, H⟩ ⟨sup a' f', H'⟩

  -- include R -- BUG WITHOUT THIS
  -- inductive rel2.{z} {a : A} (X : B a → Type.{z}) (f : Πb, X b → A)
  --   : (unit + Σ (b : B a), X b) → (unit + Σ (b : B a), X b) → Type.{max v w z} :=
  -- | Rmk : Π(b : B a) (x : X b) (r : R a ((f b x))), rel2 X f (inl star) (inr ⟨b, x⟩)

  -- check @rel2
  -- check @rel2.Rmk

  include R
  definition P (w : W a, B a) : Σ(X : Type.{max v w}), X → A :=
  begin
    induction w with a f IH,
    refine ⟨quotient (rel2 (λb, (IH b).1) (λb, (IH b).2)), _⟩,
    intro x,
    induction x with x x x' s,
    { induction x with x x,
      { exact a},
      { exact Wtype.pr1 (f x.1)}},
    { induction s, esimp, exact sorry}
  end

  -- definition PR (w : W a, B a) : Σ(P : Type), P → P → Type :=
  -- begin
  --   induction w with a f IH,
  --   --  Wtype.rec (λa f downs, unit + Σb, downs b)
  --   exact @quotient (unit + Σb, IH b) (λx y, _)
  -- end


--  definition Wsusp : Type := W_colim A B P _

  end

end Wsusp
