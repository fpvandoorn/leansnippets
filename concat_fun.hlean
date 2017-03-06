open eq

  definition concat₁ {A : Type} {a₁ a₂ a₃ : A} (p : a₁ = a₂) (q : a₂ = a₃) : a₁ = a₃ :=
  by induction q; assumption

  definition concat₂ {A : Type} {a₁ a₂ a₃ : A} (p : a₁ = a₂) (q : a₂ = a₃) : a₁ = a₃ :=
  by induction p; assumption

  definition concat₃ {A : Type} {a₁ a₂ a₃ : A} (p : a₁ = a₂) (q : a₂ = a₃) : a₁ = a₃ :=
  by induction q; induction p; reflexivity

  definition concat₄ {A : Type} {a₁ a₂ a₃ : A} (p : a₁ = a₂) (q : a₂ = a₃) : a₁ = a₃ :=
  by induction p; induction q; reflexivity

  example {A : Type} {a a' : A} (p : a = a') : ap id p = concat₁ idp p := idp
  example {A : Type} {a a' : A} (p : a = a') :       p = concat₂ idp p := idp
  example {A : Type} {a a' : A} (p : a = a') : ap id p = concat₃ idp p := idp
  example {A : Type} {a a' : A} (p : a = a') : ap id p = concat₄ idp p := idp
  example {A : Type} {a a' : A} (p : a = a') :       p = concat₁ p idp := idp
  example {A : Type} {a a' : A} (p : a = a') : ap id p = concat₂ p idp := sorry --idp
  example {A : Type} {a a' : A} (p : a = a') : ap id p = concat₃ p idp := idp
  example {A : Type} {a a' : A} (p : a = a') : ap id p = concat₄ p idp := sorry --idp

  eval λ(A : Type) (a a' : A) (p : a = a'), concat₁ p idp
  eval λ(A : Type) (a a' : A) (p : a = a'), concat₂ p idp
  eval λ(A : Type) (a a' : A) (p : a = a'), concat₃ p idp
  eval λ(A : Type) (a a' : A) (p : a = a'), concat₄ p idp
  eval λ(A : Type) (a a' : A) (p : a = a'), concat₁ idp p
  eval λ(A : Type) (a a' : A) (p : a = a'), concat₂ idp p
  eval λ(A : Type) (a a' : A) (p : a = a'), concat₃ idp p
  eval λ(A : Type) (a a' : A) (p : a = a'), concat₄ idp p
  eval λ{A : Type} {a₁ a₂ a₃ : A} (p : a₁ = a₂) (q : a₂ = a₃), concat₁ p q
  eval λ{A : Type} {a₁ a₂ a₃ : A} (p : a₁ = a₂) (q : a₂ = a₃), concat₂ p q
  eval λ{A : Type} {a₁ a₂ a₃ : A} (p : a₁ = a₂) (q : a₂ = a₃), concat₃ p q
  eval λ{A : Type} {a₁ a₂ a₃ : A} (p : a₁ = a₂) (q : a₂ = a₃), concat₄ p q

  example {A B : Type} (f : A → B) {a a' : A} (p : a = a') : ap f p = ap f (idp ⬝ p) :=
  ap_compose f id p
  example {A B : Type} (f : A → B) {a a' : A} (p : a = a') : ap f (ap id p) = ap f (idp ⬝ p) := idp
  example {A : Type} {a a' : A} (p : a = a') : ap id p = idp ⬝ p := idp
  example {A : Type} {a a' : A} (p : a = a') : ap_id p = idp_con p := idp
