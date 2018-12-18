open nat eq is_trunc


inductive vector (A : Type) : ℕ → Type :=
| nil {} : vector A zero
| cons   : Π {n}, A → vector A n → vector A (succ n)
print vector.no_confusion
open vector
notation a :: b := cons a b

definition head {A : Type} {n : ℕ} (v : vector A (n+1)) : A :=
begin
  cases v with _ a v', exact a
end

definition tail {A : Type} {n : ℕ} (v : vector A (n+1)) : vector A n :=
begin
  cases v with _ a v', exact v'
end

definition head' {A : Type} : Π {n : ℕ}, vector A (succ n) → A
| n (x :: xs) := x

definition tail' {A : Type} : Π {n : ℕ}, vector A (succ n) → vector A n
| n (x :: xs) := xs

definition cons_inj {A : Type} {n : ℕ} (a a' : A) (v : vector A n) (v' : vector A n)
  (p : a :: v = a' :: v') : a = a' × v = v' :=
begin
  injection p with p₁ p₂ p₃,
  split, exact p₂,
  have p₄ : rfl = p₁, from !is_set.elim, induction p₄,
  exact p₃
end

definition const {A : Type} : Π (n : ℕ), A → vector A n
| zero     a := nil
| (succ n) a := a :: const n a


-- theorem singlenton_vector_unit : ∀ {n : ℕ} (v w : vector unit n), v = w
-- | zero     nil        nil        := rfl
-- | (succ n) (star::xs) (star::ys) :=
--   begin
--     have h₁ : xs = ys, from singlenton_vector_unit xs ys,
--     rewrite h₁
--   end

definition swap {A : Type} : Π {n}, vector A (succ (succ n)) → vector A (succ (succ n))
| swap (a :: b :: vs) := b :: a :: vs
