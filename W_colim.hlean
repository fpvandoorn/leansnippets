import hit.quotient types.W

open eq quotient Wtype sigma equiv equiv.ops

namespace W_colim

  section
  parameters (A : Type) (B : A → Type) (P : (W a, B a) → Type)
             (g : Π⦃a : A⦄ {b : B a} {f : B a → W a, B a}, P (f b) → P (sup a f))
  variables  {a : A} (b : B a) {f : B a → W a, B a} {w : W a, B a} (p : P w) (q : Πb, P (f b))

  inductive W_rel : sigma P → sigma P → Type :=
  | Rmk : Π{a : A} {b : B a} (f : B a → W a, B a) (q : Πb, P (f b)),
          W_rel ⟨f b, q b⟩ ⟨sup a f, g (q b)⟩

  definition W_colim : Type := quotient W_rel

  parameters {A B}
  definition inclusion : W_colim :=
  class_of W_rel ⟨w, p⟩

  abbreviation wι := @inclusion

  parameters {P g}
  definition glue : wι (q b) = wι (g (q b)) :=
  eq_of_rel W_rel (W_rel.Rmk f q)

  protected definition rec {Q : W_colim → Type} (Qincl : Π⦃w : W a, B a⦄ (p : P w), Q (wι p))
    (Qglue : Π⦃a : A⦄ (b : B a) {f : B a → W a, B a} (q : Πb, P (f b)),
      Qincl (q b) =[glue b q] Qincl (g (q b))) (aa : W_colim) : Q aa :=
  begin
    induction aa with v v v' r,
    { induction v with w p, exact Qincl p},
    { induction r, apply Qglue}
  end

  protected definition rec_on [reducible] {Q : W_colim → Type} (aa : W_colim)
    (Qincl : Π⦃w : W a, B a⦄ (p : P w), Q (wι p))
    (Qglue : Π⦃a : A⦄ (b : B a) {f : B a → W a, B a} (q : Πb, P (f b)),
      Qincl (q b) =[glue b q] Qincl (g (q b))) : Q aa :=
  rec Qincl Qglue aa

  theorem rec_glue {Q : W_colim → Type} (Qincl : Π⦃w : W a, B a⦄ (p : P w), Q (wι p))
    (Qglue : Π⦃a : A⦄ (b : B a) {f : B a → W a, B a} (q : Πb, P (f b)),
      Qincl (q b) =[glue b q] Qincl (g (q b)))
    {a : A} (b : B a) {f : B a → W a, B a} (q : Πb, P (f b)) :
    apdo (rec Qincl Qglue) (glue b q) = Qglue b q :=
  !rec_eq_of_rel

  protected definition elim {Q : Type} (Qincl : Π⦃w : W a, B a⦄ (p : P w), Q)
    (Qglue : Π⦃a : A⦄ (b : B a) {f : B a → W a, B a} (q : Πb, P (f b)),
      Qincl (q b) = Qincl (g (q b))) : W_colim → Q :=
  rec Qincl (λa b f q, pathover_of_eq (Qglue b q))

  protected definition elim_on [reducible] {Q : Type} (aa : W_colim)
    (Qincl : Π⦃w : W a, B a⦄ (p : P w), Q)
    (Qglue : Π⦃a : A⦄ (b : B a) {f : B a → W a, B a} (q : Πb, P (f b)),
      Qincl (q b) = Qincl (g (q b))) : Q :=
  elim Qincl Qglue aa

  theorem elim_glue {Q : Type} (Qincl : Π⦃w : W a, B a⦄ (p : P w), Q)
    (Qglue : Π⦃a : A⦄ (b : B a) {f : B a → W a, B a} (q : Πb, P (f b)),
      Qincl (q b) = Qincl (g (q b)))
    {a : A} (b : B a) {f : B a → W a, B a} (q : Πb, P (f b))
      : ap (elim Qincl Qglue) (glue b q) = Qglue b q :=
  begin
    apply eq_of_fn_eq_fn_inv !(pathover_constant (glue b q)),
    rewrite [▸*,-apdo_eq_pathover_of_eq_ap,↑elim,rec_glue],
  end

  protected definition elim_type (Qincl : Π⦃w : W a, B a⦄ (p : P w), Type)
    (Qglue : Π⦃a : A⦄ (b : B a) {f : B a → W a, B a} (q : Πb, P (f b)),
      Qincl (q b) ≃ Qincl (g (q b))) : W_colim → Type :=
  elim Qincl (λa b f q, ua (Qglue b q))

  protected definition elim_type_on [reducible] (aa : W_colim)
    (Qincl : Π⦃w : W a, B a⦄ (p : P w), Type)
    (Qglue : Π⦃a : A⦄ (b : B a) {f : B a → W a, B a} (q : Πb, P (f b)),
      Qincl (q b) ≃ Qincl (g (q b))) : Type :=
  elim_type Qincl Qglue aa

  theorem elim_type_glue (Qincl : Π⦃w : W a, B a⦄ (p : P w), Type)
    (Qglue : Π⦃a : A⦄ (b : B a) {f : B a → W a, B a} (q : Πb, P (f b)),
      Qincl (q b) ≃ Qincl (g (q b)))
    {a : A} (b : B a) {f : B a → W a, B a} (q : Πb, P (f b))
      : transport (elim_type Qincl Qglue) (glue b q) = Qglue b q :=
  by rewrite [tr_eq_cast_ap_fn,↑elim_type,elim_glue];apply cast_ua_fn

  end

end W_colim

attribute W_colim.rec W_colim.elim [unfold 8] [recursor 8]
attribute W_colim.elim_type [unfold 7]
attribute W_colim.rec_on W_colim.elim_on [unfold 6]
attribute W_colim.elim_type_on [unfold 5]

-- namespace Wtype

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

-- end Wtype


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
