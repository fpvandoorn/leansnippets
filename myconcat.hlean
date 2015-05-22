
open nat eq

inductive lpath {A : Type} (a : A) : A → ℕ → Type :=
lidp {} : lpath a a 0,
cons : Π{n : ℕ} {b c : A} (p : b = c) (l : lpath a b n), lpath a c (succ n)

-- inductive lpath2 {A : Type} : A → A → ℕ → Type :=
-- | lidp2 : Π{a : A}, lpath2 a a 0
-- | cons2 : Π{a b c : A} {n : ℕ} (p : b = c) (l : lpath2 a b n), lpath2 a c (succ n)

variables {A : Type} {a b : A} {n : ℕ}


open lpath eq

  protected definition elim (l : lpath a b n) : a = b :=
  begin
    induction l with n b c p l q,
      exact idp,
      exact q ⬝ p
  end
