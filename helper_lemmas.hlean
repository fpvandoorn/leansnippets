/- NOT FOR BLESSED REPOSITORY -/

import types.eq types.pi hit.colimit cubical.square

open eq is_trunc unit quotient seq_colim is_equiv funext pi nat equiv

  definition eq_of_homotopy_tr {A : Type} {B : A → Type} {C : Πa, B a → Type}
    {f g : Πa, B a} {H : f ~ g} {a : A} (c : C a (f a)) :
      eq_of_homotopy H ▸ c = H a ▸ c :=
  begin
    apply (homotopy.rec_on H),
    intro p, apply (eq.rec_on p),
    rewrite (left_inv apd10 (refl f))
  end

  definition eq_of_homotopy_tr2 {A : Type} {B : A → Type} {C : Πa', B a' → Type}
    {f g : Πa, B a} (H : f ~ g) (c : Πa, C a (f a)) (a : A) :
     (transport _ (eq_of_homotopy H) c) a = H a ▸ c a  :=
  begin
    apply (homotopy.rec_on H),
    intro p, apply (eq.rec_on p),
    rewrite (left_inv apd10 (refl f))
  end

  definition ap_eq_idp {A B : Type} (f : A → B) {a : A} {p : a = a} (q : p = idp)
    : ap f p = idp :=
  ap (ap f) q

  definition ap_transport {A : Type} {B : A → Type} {f g : A → A} (p : f ~ g) {i : A → A}
    (h : Πa, B a → B (i a)) (a : A) (b : B (f a)) : ap i (p a) ▸ h (f a) b = h (g a) (p a ▸ b) :=
  homotopy.rec_on p (λq, eq.rec_on q idp)

  definition ap_pathover {A : Type} {B : A → Type} {f g : A → A} (p : f ~ g) {i : A → A}
    (h : Πa, B a → B (i a)) (a : A) (b : B (f a)) (b' : B (g a))
    (r : pathover B b (p a) b') : pathover B (h (f a) b) (ap i (p a)) (h (g a) b') :=
  by induction p; induction r using idp_rec_on; exact idpo

  definition inv_con_con_eq_of_eq_con_con_inv {A : Type} {a₁ a₂ b₁ b₂ : A} {p : a₁ = b₁}
    {q : a₁ = a₂} {r : a₂ = b₂} {s : b₁ = b₂} (H : q = p ⬝ s ⬝ r⁻¹) : p⁻¹ ⬝ q ⬝ r = s :=
  begin
    apply con_eq_of_eq_con_inv,
    apply inv_con_eq_of_eq_con,
    rewrite -con.assoc,
    apply H
  end

  definition eq_con_con_inv_of_inv_con_con_eq {A : Type} {a₁ a₂ b₁ b₂ : A} {p : a₁ = b₁}
    {q : a₁ = a₂} {r : a₂ = b₂} {s : b₁ = b₂} (H : p⁻¹ ⬝ q ⬝ r = s) : q = p ⬝ s ⬝ r⁻¹ :=
  begin
    apply eq_con_inv_of_con_eq,
    apply eq_con_of_inv_con_eq,
    rewrite -con.assoc,
    apply H
  end

  definition square_of_pi_eq {A B C : Type} (f : A → C) (g : B → C)
    {a a' : A} {b b' : B} (p : a = a') (q : b = b') (r : Πa b, f a = g b)
    : square (ap f p) (ap g q) (r a b) (r a' b') :=
  by cases p; cases q;exact hrfl

  theorem is_prop_elim_self {A : Type} {H : is_prop A} (x : A) : is_prop.elim x x = idp :=
  !is_prop.elim

  definition is_set_image_of_is_prop_image {A B : Type} {f : A → B} {a a' : A} (p q : a = a')
    (H : Π(a a' : A), f a = f a') : ap f p = ap f q :=
  have H' : Π{b c : A} (r : b = c), !H⁻¹ ⬝ H a c = ap f r, from
    (λb c r, eq.rec_on r !con.left_inv),
  !H'⁻¹ ⬝ !H'

  definition apo011_inv_con {A Z : Type} {B : A → Type} (f : Πa, B a → Z) {a a' a'' : A}
    {b : B a} {b' : B a'} {b'' : B a''} (Ha : a' = a) (Ha' : a' = a'')
    (Hb : b' =[Ha] b) (Hb' : b' =[Ha'] b'')
      : (apo011 f Ha Hb)⁻¹ ⬝ apo011 f Ha' Hb' = apo011 f (Ha⁻¹ ⬝ Ha') (Hb⁻¹ᵒ ⬝o Hb') :=
  by cases Hb; cases Hb'; reflexivity
