import types.nat.hott cubical.cubeover homotopy.join homotopy.circle ..Spectral.homotopy.smash

/---------------------------------------------------------------------------------------------------
  Show that type quotient preserves equivalence.
  Can this be done without univalence?
---------------------------------------------------------------------------------------------------/
namespace quotient
  open equiv eq
  universe variables u v
  variables {A B : Type.{u}} {R : A → A → Type.{v}} {S : B → B → Type.{v}}

  definition quotient_equiv (f : A ≃ B) (g : Π(a a' : A), R a a' ≃ S (f a) (f a'))
    : quotient R ≃ quotient S :=
  begin
    revert S g, eapply (equiv.rec_on_ua_idp f), esimp, intro S g,
    have H : R = S,
      by intros, apply eq_of_homotopy, intro a, apply eq_of_homotopy, intro a',
         eapply (equiv.rec_on_ua_idp (g a a')), reflexivity,
    cases H, reflexivity
  end
end quotient

/---------------------------------------------------------------------------------------------------
  Test of pushouts: show that the pushout of the diagram
    1 <- 0 -> 1
  is equivalent to 2.
---------------------------------------------------------------------------------------------------/
namespace pushout
  open equiv is_equiv unit bool
  private definition unit_of_empty (u : empty) : unit := star

  example : pushout unit_of_empty unit_of_empty ≃ bool :=
  begin
    fapply equiv.MK,
    { intro x, induction x with u u c,
        exact ff,
        exact tt,
        cases c},
    { intro b, cases b,
        exact (!inl ⋆),
        exact (!inr ⋆)},
    { intro b, cases b,
        reflexivity,
        reflexivity},
    { intro x, induction x with u u c,
        cases u, reflexivity,
        cases u, reflexivity,
        cases c},
  end

end pushout

/---------------------------------------------------------------------------------------------------
  (Part of) encode-decode proof to characterize the equality type of the natural numbers.
  This is not needed in the library, since we use Hedberg's Theorem to show that the natural numbers
  is a set
---------------------------------------------------------------------------------------------------/
namespace nathide
  open unit eq is_trunc nat
  protected definition code (n m : ℕ) : Type₀ :=
  begin
    revert m,
    induction n with n IH,
    { intro m, cases m,
      { exact unit},
      { exact empty}},
    { intro m, cases m with m,
      { exact empty},
      { exact IH m}},
  end

  protected definition encode {n m : ℕ} (p : n = m) : nat.code n m :=
  begin
    revert m p,
    induction n with n IH,
    { intro m p, cases m,
      { exact star},
      { contradiction}},
    { intro m p, cases m with m,
      { contradiction},
      { rewrite [↑nat.code], apply IH, injection p, assumption}},
  end

  protected definition decode {n m : ℕ} (q : nat.code n m) : n = m :=
  begin
    revert m q,
    induction n with n IH,
    { intro m q, cases m,
      { reflexivity},
      { contradiction}},
    { intro m q, cases m with m,
      { contradiction},
      { exact ap succ (!IH q)}},
  end

  definition is_prop_code (n m : ℕ) : is_prop (nat.code n m) :=
  begin
    apply is_prop.mk, revert m,
    induction n with n IH,
    { intro m p q, cases m,
      { cases p, cases q, reflexivity},
      { contradiction}},
    { intro m p q, cases m with m,
      { contradiction},
      { exact IH m p q}},
  end
  local attribute is_prop_code [instance]
end nathide

/---------------------------------------------------------------------------------------------------
  (Part of) encode-decode proof to characterize < on nat, to show that it is a mere proposition.
  In types.nat.hott there is a simpler proof
---------------------------------------------------------------------------------------------------/

namespace nat
namespace lt
  open unit is_trunc algebra
  protected definition code (n m : ℕ) : Type₀ :=
  begin
    revert m,
    induction n with n IH,
    { intro m, cases m,
      { exact empty},
      { exact unit}},
    { intro m, cases m with m,
      { exact empty},
      { exact IH m}},
  end

  protected definition encode {n m : ℕ} (p : n < m) : lt.code n m :=
  begin
    revert m p,
    induction n with n IH,
    { intro m p, cases m,
      { exfalso, exact !lt.irrefl p},
      { exact star}},
    { intro m p, cases m with m,
      { exfalso, apply !not_lt_zero p},
      { rewrite [↑lt.code], apply IH, apply lt_of_succ_lt_succ p}},
  end

  protected definition decode {n m : ℕ} (q : lt.code n m) : n < m :=
  begin
    revert m q,
    induction n with n IH,
    { intro m q, cases m,
      { contradiction},
      { apply zero_lt_succ}},
    { intro m q, cases m with m,
      { contradiction},
      { exact succ_lt_succ (!IH q)}},
  end

  definition is_prop_code (n m : ℕ) : is_prop (lt.code n m) :=
  begin
    apply is_prop.mk, revert m,
    induction n with n IH,
    { intro m p q, cases m,
      { contradiction},
      { cases p, cases q, reflexivity}},
    { intro m p q, cases m with m,
      { contradiction},
      { exact IH m p q}},
  end
  local attribute is_prop_code [instance]

end lt
end nat

/---------------------------------------------------------------------------------------------------
  Alternative recursor for inequality on ℕ
---------------------------------------------------------------------------------------------------/

namespace nat
  open eq is_trunc


  inductive le2 : ℕ → ℕ → Type :=
  | zero_le2 : Πk, le2 0 k
  | succ_le2_succ : Π{n k : ℕ}, le2 n k → le2 (succ n) (succ k)

  open le2

  definition le2_of_le {n m : ℕ} (H : n ≤ m) : le2 n m :=
  begin
    induction H with m H IH,
    { induction n with n IH,
      { exact zero_le2 0},
      { exact succ_le2_succ IH}},
    { clear H, induction IH with m n m IH IH2,
      { apply zero_le2},
      { exact succ_le2_succ IH2}}
  end

  definition le_of_le2 {n m : ℕ} (H : le2 n m) : n ≤ m :=
  begin
    induction H with m n m H IH,
    { apply zero_le},
    { apply succ_le_succ IH}
  end

  definition nat.le.rec2 {C : Π (n k : ℕ), n ≤ k → Type}
    (H1 : Πk, C 0 k (zero_le k))
    (H2 : (Π{n k : ℕ} (H : n ≤ k), C n k H → C (succ n) (succ k) (succ_le_succ H)))
    {n k : ℕ} (H : n ≤ k) : C n k H :=
  begin
    assert lem : Π(x : le2 n k), C n k (le_of_le2 x),
    { intro x, clear H,
      induction x with k n k x IH,
      { refine transport (C _ _) _ (H1 k), apply is_prop.elim},
      { refine transport (C _ _) _ (H2 (le_of_le2 x) IH), apply is_prop.elim}},
    refine transport (C _ _) _ (lem (le2_of_le H)), apply is_prop.elim
  end

end nat

/---------------------------------------------------------------------------------------------------
  [WIP] Try to see whether having a list of paths is useful
---------------------------------------------------------------------------------------------------/

namespace lpath
  open nat eq
  inductive lpath {A : Type} (a : A) : A → ℕ → Type :=
  lidp : lpath a a 0,
  cons : Π{n : ℕ} {b c : A} (p : b = c) (l : lpath a b n), lpath a c (succ n)

  open lpath.lpath

  protected definition elim {A : Type} : Π{a b : A} {n : ℕ} (l : lpath a b n), a = b
  | elim (lidp a) := idp
  | elim (cons p l) := elim l ⬝ p
end lpath

/---------------------------------------------------------------------------------------------------
  apn is weakly constant
---------------------------------------------------------------------------------------------------/

namespace apn
  open eq pointed nat

  definition weakly_constant_apn {A B : pType} {n : ℕ} {f : map₊ A B} (p : Ω[n] A)
    (H : Π(a : A), f a = pt) : apn n f p = pt :=
  begin
    induction n with n IH,
    { unfold [apn, loopn] at *, apply H},
    { exact sorry}
  end

end apn

/---------------------------------------------------------------------------------------------------
  two quotient eliminator is unique
---------------------------------------------------------------------------------------------------/

/---------------------------------------------------------------------------------------------------
  unit relation on circle
---------------------------------------------------------------------------------------------------/

namespace circlerel
  open circle equiv prod eq
  variables {A : Type} (a : A)
  inductive R : A → A → Type :=
  | Rmk : R a a
  open R

  definition R_equiv (x y) : R a x y ≃ a = x × a = y :=
  begin
    fapply equiv.MK,
    { intro r, induction r, exact (idp, idp)},
    { intro v, induction v with p₁ p₂, induction p₁, induction p₂, exact Rmk a},
    { intro v, induction v with p₁ p₂, induction p₁, induction p₂, reflexivity},
    { intro r, induction r, reflexivity}
  end

  definition R_circle : R base base base ≃ ℤ × ℤ :=
  !R_equiv ⬝e prod_equiv_prod base_eq_base_equiv base_eq_base_equiv

end circlerel

/---------------------------------------------------------------------------------------------------
  Quotienting A with the diagonal relation (smallest reflexive relation) gives A × S¹
---------------------------------------------------------------------------------------------------/

namespace circle

  open eq circle prod quotient equiv

  section
  parameter {A : Type}

  inductive reflexive_rel : A → A → Type :=
  | Rmk : Πx, reflexive_rel x x
  open reflexive_rel

  definition times_circle := quotient reflexive_rel

  definition φ [unfold 2] (x : times_circle) : A × S¹ :=
  begin
    induction x,
    { exact (a, base)},
    { induction H, exact ap (pair x) loop}
  end

  definition ψ [unfold 2] (x : A × S¹) : times_circle :=
  begin
    induction x with x y, induction y,
    { exact class_of _ x},
    { apply eq_of_rel, exact Rmk x}
  end

  definition times_circle_equiv [constructor] : times_circle ≃ A × S¹ :=
  begin
    fapply equiv.MK,
    { exact φ},
    { exact ψ},
    { intro x, induction x with x y, induction y,
      { reflexivity},
      { apply eq_pathover, apply hdeg_square,
        rewrite [ap_compose φ (λa, ψ (x, a)), ▸*, elim_loop, ↑φ], apply elim_eq_of_rel}},
    { intro x, induction x,
      { reflexivity},
      { apply eq_pathover, apply hdeg_square, rewrite [ap_id], refine ap_compose ψ φ _ ⬝ _,
        refine ap (ap ψ) !elim_eq_of_rel ⬝ _, induction H, esimp,
        refine !ap_compose⁻¹ ⬝ _, esimp [function.compose], apply elim_loop}}
  end

  /- the same construction, where the relation is equivalent, but defined differently -/

  definition reflexive_rel2 := @eq A

  definition times_circle2 := quotient reflexive_rel2

  definition φ' [unfold 2] (x : times_circle2) : A × S¹ :=
  begin
    induction x,
    { exact (a, base)},
    { induction H, exact ap (pair a) loop}
  end

  definition ψ' [unfold 2] (x : A × S¹) : times_circle2 :=
  begin
    induction x with x y, induction y,
    { exact class_of _ x},
    { apply eq_of_rel, apply idp}
  end

  definition times_circle2_equiv [constructor] : times_circle2 ≃ A × S¹ :=
  begin
    fapply equiv.MK,
    { exact φ'},
    { exact ψ'},
    { intro x, induction x with x y, induction y,
      { reflexivity},
      { apply eq_pathover, apply hdeg_square,
        rewrite [ap_compose φ' (λa, ψ' (x, a)), ▸*, elim_loop, ↑φ'], apply elim_eq_of_rel}},
    { intro x, induction x,
      { reflexivity},
      { apply eq_pathover, apply hdeg_square, rewrite [ap_id], refine ap_compose ψ' φ' _ ⬝ _,
        refine ap (ap ψ') !elim_eq_of_rel ⬝ _, induction H, esimp,
        refine !ap_compose⁻¹ ⬝ _, esimp [function.compose], apply elim_loop}}
  end

  end

end circle

/---------------------------------------------------------------------------------------------------

---------------------------------------------------------------------------------------------------/

namespace pushout

  open eq pi

  variables {TL BL TR : Type} {f : TL → BL} {g : TL → TR}

  protected definition elim_type' [unfold 9] (Pinl : BL → Type) (Pinr : TR → Type)
    (Pglue : Π(x : TL), Pinl (f x) ≃ Pinr (g x)) : pushout f g → Type :=
  pushout.elim Pinl Pinr (λx, ua (Pglue x))

  protected definition elim_type_eq {Pinl : BL → Type} {Pinr : TR → Type}
    (Pglue : Π(x : TL), Pinl (f x) ≃ Pinr (g x)) (y : pushout f g) :
    pushout.elim_type Pinl Pinr Pglue y ≃ pushout.elim_type' Pinl Pinr Pglue y :=
  begin
    fapply equiv.MK,
    { induction y, exact id, exact id, apply arrow_pathover_left, esimp, intro,
      apply pathover_of_tr_eq, exact sorry},
    { induction y, exact id, exact id, apply arrow_pathover_left, esimp, intro,
      apply pathover_of_tr_eq, exact sorry},
    { intro b, induction y, reflexivity, reflexivity, esimp,
      apply pi_pathover_left, intro b, esimp at *, exact sorry},
    { exact sorry},
  end

/---------------------------------------------------------------------------------------------------
  define quotient from pushout
---------------------------------------------------------------------------------------------------/


namespace pushout
  open quotient sum sigma sigma.ops
  section
  parameters {A : Type} (R : A → A → Type)

  definition f [unfold 3] : A + (Σx y, R x y) → A
  | (sum.inl a) := a
  | (sum.inr v) := v.1

  definition g [unfold 3] : A + (Σx y, R x y) → A
  | (sum.inl a) := a
  | (sum.inr v) := v.2.1

  definition X [reducible] := pushout f g
  definition Q [reducible] := quotient R
  definition X_of_Q [unfold 3] : Q → X :=
  begin
    intro q, induction q,
    { exact inl a},
    { exact glue (sum.inr ⟨a, a', H⟩) ⬝ (glue (sum.inl a'))⁻¹}
  end

  definition Q_of_X [unfold 3] : X → Q :=
  begin
    intro x, induction x,
    { exact class_of R a},
    { exact class_of R a},
    { cases x with a v,
      { reflexivity},
      { exact eq_of_rel R v.2.2}}
  end

  definition Q_of_X_of_Q (q : Q) : Q_of_X (X_of_Q q) = q :=
  begin
    induction q,
    { reflexivity},
    { apply eq_pathover_id_right, apply hdeg_square, refine ap_compose Q_of_X _ _ ⬝ _,
      refine ap02 Q_of_X !elim_eq_of_rel ⬝ _, refine !ap_con ⬝ _,
      refine whisker_left _ !ap_inv ⬝ _,
      exact !elim_glue ◾ !elim_glue⁻²}
  end

  definition X_of_Q_of_X (x : X) : X_of_Q (Q_of_X x) = x :=
  begin
    induction x,
    { reflexivity},
    { esimp, exact glue (sum.inl x)},
    { apply eq_pathover_id_right,
      refine ap_compose X_of_Q _ _ ⬝ph _,
      refine ap02 X_of_Q !elim_glue ⬝ph _,
      cases x with a v,
      { esimp, exact square_of_eq idp},
      { cases v with a₁ v, cases v with a₂ r, esimp, refine !elim_eq_of_rel ⬝ph _,
        apply square_of_eq, refine !idp_con ⬝ _, exact !inv_con_cancel_right⁻¹}}
  end

  end
end pushout

/---------------------------------------------------------------------------------------------------
Is the suspension of sets without decidable equality a 1-type?
---------------------------------------------------------------------------------------------------/

namespace susp

  section
  open susp eq bool is_trunc quotient unit pointed equiv prod int
  parameter (P : Prop.{0})
  inductive R : bool → bool → Type :=
  | Rmk : P → R ff tt

  definition Xt := quotient R
  definition X : Type* := pointed.MK Xt (class_of R ff)
  definition npt : X := class_of R tt
  definition pth (p : P) : pt = npt :> X := eq_of_rel R (R.Rmk p)

  /- X is a pointed set -/

  definition code [unfold 2] : X → Prop.{0} :=
  begin
    intro x, induction x with b,
    { induction b, exact trunctype.mk unit _, exact P},
    { induction H, esimp, apply tua, esimp, apply equiv_of_is_prop,
      { intro u, exact a },
      { intro p, exact ⋆ }}
  end

  definition encode [unfold 3] (x : X) (p : pt = x) : code x :=
  transport code p ⋆

  definition decode [unfold 2 3] (x : X) (c : code x) : pt = x :=
  begin
    induction x with b,
    { induction b,
      { reflexivity },
      { esimp at c, exact pth c }},
    { induction H with p, apply arrow_pathover_left, intro c,
      apply eq_pathover_constant_left_id_right, esimp at *, apply square_of_eq,
      refine !idp_con ⬝ _ ⬝ !idp_con⁻¹, apply ap pth !is_prop.elim }
  end

  definition decode_encode (x : X) (p : pt = x) : decode x (encode x p) = p :=
  begin
    induction p, reflexivity
  end

  definition encode_decode (x : X) (c : code x) : encode x (decode x c) = c :=
  !is_prop.elim

  definition X_eq [constructor] (x : X) : (pt = x) ≃ code x :=
  equiv.MK (encode x) (decode x) (encode_decode x) (decode_encode x)

  definition X_flip [unfold 2] (x : X) : X :=
  begin
    induction x with b,
    { exact class_of _ (bnot b) },
    { induction H with p, exact (pth p)⁻¹ },
  end

  attribute bnot bnot_bnot [unfold 1]
  definition X_flip_flip [unfold 2] (x : X) : X_flip (X_flip x) = x :=
  begin
    induction x with b,
    { exact ap (class_of R) !bnot_bnot },
    { induction H with p, apply eq_pathover_id_right, apply hdeg_square,
      krewrite [ap_compose' X_flip X_flip, ↑X_flip, elim_eq_of_rel, ▸*, ap_inv, elim_eq_of_rel, ▸*],
      apply inv_inv },
  end

  definition X_flip_equiv [constructor] : X ≃ X :=
  equiv.MK X_flip X_flip X_flip_flip X_flip_flip

  definition is_set_X [instance] : is_set X :=
  begin
    apply is_trunc_succ_intro,
    intro x y,
    induction x using quotient.rec_prop with b,
    assert H : Π(y : X), is_prop (pt = y),
    { intro y, exact is_trunc_equiv_closed_rev _ (X_eq y) },
    induction b,
    { apply H },
    { apply @(is_trunc_equiv_closed_rev _ (eq_equiv_fn_eq_of_equiv X_flip_equiv npt y)),
      apply H }
  end

  definition Xs [constructor] : Set := trunctype.mk X _

  definition Y := psusp X
  definition tℤ : Set := trunctype.mk ℤ _

  definition loop : pt = pt :> Y :=
  merid npt ⬝ (merid pt)⁻¹

  definition Ycode [unfold 2] : Y → Set.{0} :=
  begin
    intro y, induction y with x,
    { exact tℤ }, --if P then unit else ℤ, except implement it using quotients with paths from P
    { exact tℤ }, --
    { apply tua, induction x with b,
      { induction b,
        { reflexivity },
        { apply equiv_succ }},
      { induction H with p, esimp, apply equiv_eq, intro x, exact sorry }}
  end

  definition Yencode [unfold 3] (y : Y) (p : pt = y) : Ycode y :=
  transport Ycode p (0 : ℤ)

  definition Ydecode [unfold 2 3] (y : Y) (c : Ycode y) : pt = y :=
  begin
    induction y with b,
    { exact power loop c },
    { exact power loop c ⬝ merid pt },
    { apply arrow_pathover_left, intro c,
      apply eq_pathover_constant_left_id_right, esimp at *, exact sorry }
  end

  definition Ydecode_encode (y : Y) (p : pt = y) : Ydecode y (Yencode y p) = p :=
  begin
    induction p, reflexivity
  end

  definition Yencode_decode (y : Y) (c : Ycode y) : Yencode y (Ydecode y c) = c :=
  begin
    induction y,
    { exact sorry },
    { exact sorry },
    { apply is_prop.elimo }
  end


  end
end susp

/---------------------------------------------------------------------------------------------------
Suspension of a prop
---------------------------------------------------------------------------------------------------/

namespace susp
  open is_trunc trunc_index

  definition susp_of_is_prop (A : Type) [is_prop A] : is_set (susp A) :=
  begin
    apply is_trunc_succ_of_is_trunc_loop, apply algebra.le.refl,
    intro x, induction x using susp.rec_prop,

  end

end susp

/---------------------------------------------------------------------------------------------------
start on the proof that susp (smash A B) = reduced_join A B
Here we use the join, which is equivalent(?)
---------------------------------------------------------------------------------------------------/
namespace smash
  open susp join smash pointed susp
  variables {A B : Type*}
  definition psusp_smash_of_pjoin [unfold 3] (x : pjoin A B) : psusp (smash A B) :=
  begin
    induction x with a b a b,
    { exact pt },
    { exact south },
    { exact merid (smash.mk a b) },
  end

  definition pjoin_of_psusp_smash_merid [unfold 3] (x : smash A B) : inl pt = inr pt :> pjoin A B :=
  begin
    induction x,
    { exact join.glue pt b ⬝ (join.glue a b)⁻¹ ⬝ join.glue a pt },
    { exact join.glue pt pt },
    { exact join.glue pt pt },
    { apply inv_con_cancel_right },
    { exact whisker_right _ !con.right_inv ⬝ !idp_con, }
  end

  definition pjoin_of_psusp_smash [unfold 3] (x : psusp (smash A B)) : pjoin A B :=
  begin
    induction x,
    { exact pt },
    { exact inr pt },
    { exact pjoin_of_psusp_smash_merid a },
  end

  definition psusp_smash_pequiv_pjoin : psusp (smash A B) ≃* pjoin A B :=
  begin
    fapply pequiv_of_equiv,
    { fapply equiv.MK,
      { exact pjoin_of_psusp_smash },
      { exact psusp_smash_of_pjoin },
      { intro x, induction x: esimp,
        { exact join.glue pt pt ⬝ (join.glue x pt)⁻¹ },
        { exact (join.glue pt pt)⁻¹ ⬝ join.glue pt y },
        { apply eq_pathover_id_right,
          rewrite [ap_compose' pjoin_of_psusp_smash, ↑psusp_smash_of_pjoin, join.elim_glue],
          rewrite [↑pjoin_of_psusp_smash, elim_merid, ▸*],
          exact sorry}},
      { exact sorry}},
    { reflexivity }

  end
end smash


/---------------------------------------------------------------------------------------------------
  define dependent computation rule of the circle from the other data?
---------------------------------------------------------------------------------------------------/

namespace circlecomp
  section
  open circle eq sigma sigma.ops function equiv

  parameters {P : circle → Type} (Pbase : P base) (Ploop : Pbase =[loop] Pbase)
  include Ploop

  definition eq2_pr1 {A : Type} {B : A → Type} {u v : Σa, B a} {p q : u = v} (r : p = q)
    : p..1 = q..1 :=
  ap eq_pr1 r

  definition eq2_pr2 {A : Type} {B : A → Type} {u v : Σa, B a} {p q : u = v} (r : p = q)
    : p..2 =[eq2_pr1 r] q..2 :=
  !pathover_ap (apd eq_pr2 r)

  -- definition natural_square_tr_loop {A : Type} {B : Type} {a : A} {f g : A → B}
  --   (p : f ~ g) (q : a = a) : natural_square_tr p q = _ :=
  -- _

  definition pathover_ap_id {A : Type} {a a₂ : A} (B : A → Type) {p : a = a₂}
    {b : B a} {b₂ : B a₂} (q : b =[p] b₂) : pathover_ap B id q = change_path (ap_id p)⁻¹ q :=
  by induction q; reflexivity

  definition pathover_ap_compose {A A' A'' : Type} {a a₂ : A} (B : A'' → Type)
    (g : A' → A'') (f : A → A') {p : a = a₂} {b : B (g (f a))} {b₂ : B (g (f a₂))}
    (q : b =[p] b₂) : pathover_ap B (g ∘ f) q
    = change_path (ap_compose g f p)⁻¹ (pathover_ap B g (pathover_ap (B ∘ g) f q)) :=
  by induction q; reflexivity

  definition pathover_ap_compose_rev {A A' A'' : Type} {a a₂ : A} (B : A'' → Type)
    (g : A' → A'') (f : A → A') {p : a = a₂} {b : B (g (f a))} {b₂ : B (g (f a₂))}
    (q : b =[p] b₂) : pathover_ap B g (pathover_ap (B ∘ g) f q)
    = change_path (ap_compose g f p) (pathover_ap B (g ∘ f) q) :=
  by induction q; reflexivity

  definition f : S¹ → sigma P := circle.elim ⟨base, Pbase⟩ (sigma_eq loop Ploop)
  definition g : Πx, P x := circle.rec Pbase Ploop

  definition foo1 (x : S¹) : (f x).1 = x :=
  circle.rec_on x idp
  begin apply eq_pathover, apply hdeg_square,
    rewrite [ap_id, ap_compose pr1 f,↑f,elim_loop], apply sigma_eq_pr1 end


  definition apd_eq_apd_ap {A B : Type} {C : B → Type} (g : Πb, C b) (f : A → B) {a a' : A}
    (p : a = a') : apd (λx, g (f x)) p = pathover_of_pathover_ap C f (apd g (ap f p)) :=
  by induction p; reflexivity

  definition foo2 (x : S¹) : (f x).2 =[foo1 x] g x :=
  circle.rec_on x idpo
  begin
    apply pathover_pathover, esimp, --rewrite pathover_ap_id,
    apply transport (λx, squareover P x _ _ _ _),
    apply to_left_inv !hdeg_square_equiv, esimp,
    apply hdeg_squareover,
    rewrite [pathover_ap_id, apd_eq_apd_ap pr2 f loop, ],
    exact sorry --unfold natural_square_tr,
  end

  definition p : ap f loop = (sigma_eq loop Ploop) := !elim_loop
  definition q : (ap f loop)..1 = loop := ap eq_pr1 p ⬝ !sigma_eq_pr1
  definition r : (ap f loop)..2 =[q] Ploop :=
  !eq2_pr2 ⬝o !sigma_eq_pr2

--set_option pp.notation false
  theorem my_rec_loop  : apd (circle.rec Pbase Ploop) loop = Ploop :=
  begin
    refine _ ⬝ tr_eq_of_pathover r, exact sorry
  end

  end
end circlecomp

  /- try to use the circle to transport the computation rule from the circle to the new type -/
namespace circlecomp2

  open circle eq sigma sigma.ops function equiv is_equiv

  definition X : Type₀ := circle
  definition b : X := base
  definition l : b = b := loop
  definition elim {C : Type} (c : C) (p : c = c) (x : X) : C := circle.elim c p x
  definition rec {C : X → Type} (c : C b) (p : c =[l] c) (x : X) : C x := circle.rec c p x
  theorem elim_l {C : Type} (c : C) (p : c = c) : ap (elim c p) l = p := elim_loop c p

  attribute X l [irreducible]
  attribute rec elim [unfold 4] [recursor 4]
  attribute b [constructor]

  example {C : Type} (c : C) (p : c = c) : elim c p b = c := begin esimp end

  definition XequivS : S¹ ≃ X :=
  begin
    fapply equiv.MK,
    { intro y, induction y, exact b, exact l},
    { intro x, induction x, exact base, exact loop},
    { intro x, induction x, esimp, apply eq_pathover, apply hdeg_square,
      rewrite [ap_id,ap_compose (circle.elim b l),elim_l], apply elim_loop},
    { intro y, induction y, esimp, apply eq_pathover, apply hdeg_square,
      rewrite [ap_id,ap_compose (elim base loop),elim_loop], apply elim_l},
  end

  definition is_circle (X : Type) : Type :=
  Σ(x₀ : X)
   (p : x₀ = x₀)
   (rec : Π(C : X → Type) (c : C x₀) (q : c =[p] c) (x : X), C x)
   (rec_x₀ : Π(C : X → Type) (c : C x₀) (q : c =[p] c), rec C c q x₀ = c),
   Π(C : X → Type) (c : C x₀) (q : c =[p] c), squareover C vrfl (apd (rec C c q) p) q (pathover_idp_of_eq !rec_x₀) (pathover_idp_of_eq !rec_x₀)

  definition is_circle_circle : is_circle S¹ :=
  ⟨base, loop, @circle.rec, by intros; reflexivity, begin intros, apply vdeg_squareover, apply rec_loop end⟩

  definition is_circle_X {X : Type₀} (f : S¹ ≃ X) : is_circle X :=
  transport is_circle (ua f) is_circle_circle

  namespace new
  definition b : X := (is_circle_X XequivS).1
  definition l : b = b := (is_circle_X XequivS).2.1
  definition rec : Π{C : X → Type} (c : C b) (p : c =[l] c) (x : X), C x := (is_circle_X XequivS).2.2.1
  definition rec_pt : Π{C : X → Type} (c : C b) (p : c =[l] c), rec c p b = c := (is_circle_X XequivS).2.2.2.1
--  definition rec_loop : Π{C : X → Type} (c : C b) (p : c =[l] c), squareover C vrfl (apd (rec c p) l) p (pathover_idp_of_eq !rec_pt) (pathover_idp_of_eq !rec_pt) := proof (is_circle_X XequivS).2.2.2.2 qed
  end new

  -- --set_option pp.notation false
  -- definition foo {A A' : Type} (f : A ≃ A') (B : A → Type) {a a' : A} {p : a = a'}
  --   {b : B a} {b' : B a'} : b =[p] b' ≃
  -- pathover (B ∘ to_inv f) ((to_left_inv f a)⁻¹ ▸ b) (ap (to_fun f) p) ((to_left_inv f a')⁻¹ ▸ b') :=
  -- begin
  --   induction p, esimp,
  --   refine !pathover_idp ⬝e _ ⬝e !pathover_idp⁻¹ᵉ,
  --   apply eq_equiv_fn_eq
  -- end

  -- theorem rec_l {C : X → Type} (c : C b) (p : c =[l] c) : apdo (rec c p) l = p :=
  -- begin
  --   refine eq_of_fn_eq_fn !(foo XequivS) _,
  -- end

end circlecomp2

namespace merely_decidable_equality

open eq trunc is_trunc function equiv is_equiv decidable

definition decidable_equiv_closed {A B : Type} (e : A ≃ B) (H : decidable A)
 : decidable B :=
 begin
   apply decidable_of_decidable_of_iff H,
   split, exact to_fun e, exact to_inv e
 end

local attribute is_trunc_decidable [instance]
example {A : Type} : decidable_eq (trunc 0 A) ↔
  decidable_rel (λa a' : A, trunc -1 (a = a')) :=
begin
  constructor: intro H,
  { intro a a', refine decidable_equiv_closed !tr_eq_tr_equiv (H (tr a) (tr a')) },
  { intro a a', induction a with a, induction a' with a',
    refine decidable_equiv_closed _ (H a a'),
    exact !tr_eq_tr_equiv⁻¹ᵉ
  }
end

end merely_decidable_equality

end pushout
