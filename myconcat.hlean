
exit

open nat eq

inductive lpath {A : Type} (a : A) : A → ℕ → Type :=
lidp : lpath a a 0,
cons : Π{n : ℕ} {b c : A} (p : b = c) (l : lpath a b n), lpath a c (succ n)

inductive lpath2 {A : Type} : A → A → ℕ → Type :=
| lidp2 : Π{a : A}, lpath2 a a 0
| cons2 : Π{a b c : A} {n : ℕ} (p : b = c) (l : lpath2 a b n), lpath2 a c (succ n)

variables {A : Type} {a b : A} {n : ℕ}


open lpath lpath2 unit

check @lidp
check @cons

--this gives a bug, is this my fault or Lean's fault??
  protected definition elim : Π{b : A} {n : ℕ} (l : lpath a b n), unit
  | elim (@lidp A a) := star
  | elim (@cons A a n b c p l)  := star


  protected definition elim : Π{b : A} {n : ℕ} (l : lpath a b n), a = b
  | elim (@lidp A a) := idpath a
  | elim (@cons A a n b c p l)  := elim l ⬝ p

  protected definition elim2 : Π{a : A} {b : A} {n : ℕ} (l : lpath2 a b n), a = b
  | elim2 (@lidp2 A a) := _
  | elim2 (@cons2 A a b c n p l)  := _
