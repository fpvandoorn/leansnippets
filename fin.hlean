/-
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Finite types as inductive definition.

The definition in types/fin is different, namely as a subtype of the natural numbers.
That definition doesn't allow pattern matching.
-/

import types.nat.div types.nat.hott types.prod
open eq nat bool prod algebra

inductive is_succ [class] : ℕ → Type₀ :=
| mk : Πn, is_succ (succ n)

attribute is_succ.mk [instance]

definition is_succ_add_right [instance] (n m : ℕ) [H : is_succ m] : is_succ (n+m) :=
by induction H with m; constructor

definition is_succ_add_left (n m : ℕ) [H : is_succ n] : is_succ (n+m) :=
by induction H with n; cases m with m: constructor

definition is_succ_bit0 [instance] (n : ℕ) [H : is_succ n] : is_succ (bit0 n) :=
by induction H with n; constructor

theorem fn_eq_mod {n : ℕ} {f : ℕ → ℕ}
  (H0 : f 0 = 0) (H1 : Πx, f x < n → f (succ x) = succ (f x))
  (H2 : Πx, f x = n → f (succ x) = 0) : Πx, f x = x % (succ n) :=
begin
  assert H3 : Πx, x ≤ n → f x = x,
  { intro x H,
    induction x with x IH,
    { exact H0},
    { have IH' : f x = x, from IH (le.trans !self_le_succ H),
      refine H1 x _ ⬝ ap succ IH',
      rewrite IH', exact lt_of_succ_le H}},
  assert H4 : Πx, f x ≤ n,
  { intro x, induction x using nat.rec_on with x IH ,
    { rewrite [H0], apply zero_le},
    { eapply @nat.lt_ge_by_cases (f x) n: intro H,
      { rewrite [H1 x H], exact succ_le_of_lt H},
      { have H5 : f x = n, from le.antisymm IH H,
        rewrite [H2 x H5], apply zero_le}}},
  assert H5 : Πx, f (succ n + x) = f x,
  { intro x, induction x using nat.rec_on with x IH ,
    { rewrite [add_zero, H0], apply H2, exact H3 n !le.refl},
    { eapply @nat.lt_ge_by_cases (f x) n: intro H,
      { have H' : f (succ n + x) < n, from IH⁻¹ ▸ H,
        rewrite [H1 x H, add_succ, H1 (succ n + x) H'], exact ap succ IH},
      { have H5 : f x = n, from le.antisymm (H4 x) H,
        rewrite [add_succ, H2 x H5, H2 (succ n + x) (IH ⬝ H5)]}}},
  intro x,
  induction x using nat.case_strong_rec_on with x IH,
  { exact H0},
  { eapply @nat.lt_ge_by_cases x n: intro H,
    { refine H3 (succ x) (succ_le_of_lt H) ⬝ _, symmetry,
      exact mod_eq_of_lt (succ_lt_succ H)},
    { assert H6 : succ x = succ n + (succ x - succ n),
      { symmetry, rewrite [add.comm], exact nat.sub_add_cancel (succ_le_succ H)},
      assert H7 : succ x - succ n ≤ x,
      { apply le_of_lt_succ, apply sub_lt: apply !succ_pos},
      rewrite [H6, H5, IH _ H7],
      exact !add_mod_self_left⁻¹}}
end

inductive ifin : ℕ → Type₀ := -- inductively deinclne incln-type
| max : Π n, ifin (succ n)
| incl : Π {n}, ifin n → ifin (succ n)

namespace ifin
  /-
     Intuition behind the following deinclnitions:
     max n    is (n : ifin (succ n))
     incl  sends (x : ifin n) to (x : ifin (n+1)).
     zero n   is (0 : ifin (succ n))
     succ' sends (x : ifin n) to (x+1 : ifin (n+1))
     succ' sends (x : ifin n) to (x+1 : ifin (n+1))
     succ  sends (x : ifin n) to (x+1 : ifin n) (sending n-1 to 0)
     add   sends (x y : ifin n) to (x+y ifin n), where addition is modulo n
     proj  sends (x : ifin (n+2)) to (x : ifin (n+1)) (sending n+1 to n)

     pred' sends (x : ifin n) to (x+1 : ifin n) (sending 0 to 0)
     is_zero tests whether (x : ifin n) is n-1
     pred  sends (x : ifin n) to (x+1 : ifin n) (sending 0 to n-1)
  -/

  definition zero : Π(n : ℕ), ifin (succ n)
  | 0        := max 0
  | (succ n) := incl (zero n)

  definition succ' : Π{n : ℕ}, ifin n → ifin (succ n)
  | (succ n) (max n)  := max (succ n)
  | (succ n) (incl x) := incl (succ' x)

  protected definition succ : Π{n : ℕ}, ifin n → ifin n
  | (nat.succ n) (max n)  := zero n
  | (nat.succ n) (incl x) := succ' x

  definition proj : Π{n : ℕ}, ifin (succ (succ n)) → ifin (succ n)
  | n (max (succ n)) := max n
  | n (incl x)       := x

  -- definition is_incl [reducible] : Π{n : ℕ} (x : ifin n), Type₀
  -- | 1     x := empty
  -- | (n+2) x := x = incl (proj x)

  -- definition reverse : Π{n : ℕ}, ifin n → ifin n
  -- | (nat.succ n) (max n)  := zero n
  -- | (nat.succ n) (incl x) := succ' (reverse x)

  -- definition pred' : Π{n : ℕ}, ifin n → ifin n
  -- | 1     (max 0)     := max 0
  -- | (n+2) (max (n+1)) := incl (max n)
  -- | (n+2) (incl x)    := incl (pred' x)

  -- definition is_zero : Π{n : ℕ}, ifin n → bool
  -- | 1     (max 0)     := tt
  -- | (n+2) (max (n+1)) := ff
  -- | (n+2) (incl x)    := is_zero x

  -- definition pred : Π{n : ℕ}, ifin n → ifin n
  -- | (succ n) x := cond (is_zero x) (max n) (pred' x)

  -- definition rev_add {n : ℕ} (x : ifin n): Π{m : ℕ}, ifin m → ifin n
  -- | (succ m) (max m)  := iterate ifin.succ m x
  -- | (succ m) (incl y) := rev_add y

  definition add' {n : ℕ} (x : ifin n): Π{m : ℕ}, ifin m → ifin n
  | (succ m) (max m)  := iterate ifin.succ m x
  | (succ m) (incl y) := add' y

  definition add [reducible] {n : ℕ} (x y : ifin n) : ifin n :=
  add' x y

  definition nat_of_ifin : Π{n : ℕ}, ifin n → ℕ
  | (succ n) (max n)  := n
  | (succ n) (incl x) := nat_of_ifin x

  definition ifin_of_nat (n : ℕ) : ℕ → ifin (succ n)
  | 0        := zero n
  | (succ k) := ifin.succ (ifin_of_nat k)

  definition has_zero_ifin [instance] (n : ℕ) [H : is_succ n] : has_zero (ifin n) :=
  by induction H with n; exact has_zero.mk (zero n)

  definition has_one_ifin [instance] (n : ℕ) [H : is_succ n] : has_one (ifin n) :=
  by induction H with n; exact has_one.mk (ifin.succ (zero n))

  definition has_add_ifin [instance] (n : ℕ) : has_add (ifin n) :=
  has_add.mk (add)

  /- some theorems. -/

  definition nat_of_ifin_zero (n : ℕ) : nat_of_ifin (zero n) = 0 :=
  begin
    induction n with n IH,
    { reflexivity},
    { exact IH}
  end

  definition nat_of_ifin_succ' : Π{n : ℕ} (x : ifin n),
    nat_of_ifin (succ' x) = succ (nat_of_ifin x)
  | (succ n) (max n)  := idp
  | (succ n) (incl x) := nat_of_ifin_succ' x

  definition nat_of_ifin_lt : Π{n : ℕ} (x : ifin n), nat_of_ifin x < n
  | (succ n) (max n)  := self_lt_succ n
  | (succ n) (incl x) := lt.trans (nat_of_ifin_lt x) (self_lt_succ n)

  definition nat_of_ifin_incl_neq {n : ℕ} (x : ifin n) : nat_of_ifin (incl x) ≠ n :=
  begin
    intro H,
    refine lt_le_antisymm (nat_of_ifin_lt x) _,
    apply le_of_eq, symmetry, exact H
  end

  definition add'_zero {n : ℕ} (x : ifin n) : Πm, add' x (zero m) = x
  | 0        := idp
  | (succ m) := add'_zero m

  definition add_zero {n : ℕ} (x : ifin (succ n)) : x + 0 = x :=
  add'_zero x n

  -- definition add'_succ {n : ℕ} (x : ifin n)
  --   : Π{m} (y : ifin m), add' x (ifin.succ y) = ifin.succ (add' x y)
  -- | (succ m) (max m)  := add'_zero x m ⬝ _
  -- | (succ m) (incl y) := sorry --incl (succ' x)

  -- definition iterate_succ_incl : Π{n : ℕ} (x : ifin n),
  --   iterate ifin.succ n (incl x) = incl (iterate ifin.succ)
  -- | 1 (max 0) := idp
  -- | (succ (n+1)) x   := begin esimp [iterate] end

  definition my_nat_rec {P : ℕ → ℕ → Type}
    (H0 : P 0 0)
    (H1 : Πn, P n 0 → P 0 (succ n))
    (H1 : Πn k, P n (succ k) → P (succ n) k) (n m : ℕ) : P n m := sorry

  definition incl_zero (n : ℕ) : incl (0 : ifin (succ n)) = 0 := idp

  definition succ_incl {n : ℕ} (x : ifin n) : ifin.succ (incl x) = succ' x := idp

  definition succ_incl_incl {n : ℕ} {x : ifin n}
    : ifin.succ (incl (incl x)) = incl (ifin.succ (incl x)) := idp

  -- definition succ_incl_of_is_incl : Π{n : ℕ} {x : ifin n} (H : is_incl x),
  --   ifin.succ (incl x) = incl (ifin.succ x)
  -- | 1     x           H := by cases H
  -- | (n+2) (max (n+1)) H := by cases H
  -- | (n+2) (incl x)    H := by reflexivity

  -- definition is_incl_incl : Π{n : ℕ} (x : ifin n), is_incl (incl x)
  -- | (succ n) x := idp

  definition iterate_succ_right {A : Type} (f : A → A) (n : ℕ) (x : A)
    : iterate f (succ n) x = iterate f n (f x) :=
  begin
    induction n with n IH,
    { reflexivity},
    { exact ap f IH}
  end

  definition iterate_succ_left {A : Type} (f : A → A) (n : ℕ) (x : A)
    : iterate f (succ n) x = f (iterate f n x) := idp

  -- set_option pp.notation false
  -- set_option pp.implicit true
  -- set_option pp.numerals false

  -- definition iterate_succ_zero_eq_max_lem_type [reducible]

  theorem iterate_succ_zero_eq_max_lem (n k : ℕ)
    : iterate ifin.succ (succ n) (incl (iterate ifin.succ k 0)) = max (succ (n + k)) ×
      Πm, m < n + k → iterate ifin.succ m (0 : ifin (succ (succ (pred (n + k)))))
              = incl (iterate ifin.succ m (0 : ifin (succ (pred (n + k))))) :=
  begin
    refine my_nat_rec _ _ _ n k: clear n k,
    { split,
      { reflexivity},
      { intro m H, cases H}},
    { intro n H, rewrite [zero_add (succ n), nat.add_zero n at H],
      esimp [iterate], cases H with H H2, split,
      { refine ap ifin.succ (ap incl H)},
      { intro m, induction m with m IH: intro H,
        { reflexivity},
        { note IH' := IH (lt.trans !self_lt_succ H),
          note H3 := H2 m (lt_of_succ_lt_succ H),
          rewrite [iterate_succ_left, IH'], exact sorry }}},
    { intro n k H, cases H with H H2, split,
      { refine !iterate_succ_right ⬝ _,
        rewrite [nat.succ_add], refine _ ⬝ H,
        apply ap (ifin.succ^[nat.succ n]),
        note H3 := H2 k (lt_of_le_of_lt !le_add_left !self_lt_succ),
        xrewrite [H3, succ_incl_incl, -H3]},
      { rewrite [succ_add], exact H2}}
  end

  definition iterate_succ_zero_eq_max (n : ℕ) : iterate ifin.succ (succ n) 0 = max (succ n) :=
  proof pr1 (iterate_succ_zero_eq_max_lem n 0) qed

  definition iterate_succ_eq_self : Π{n : ℕ} (x : ifin n), iterate ifin.succ n x = x
  | 1 (max 0)      := idp
  | (succ (n+1)) x := begin exact sorry end

  -- definition add_succ : Π{n : ℕ} (x y : ifin n), x + (ifin.succ y) = ifin.succ (x + y)
  -- | (succ n) x        (max n)  := add_zero x ⬝ _
  -- | (succ n) (max n)  (incl y) := sorry
  -- | (succ n) (incl x) (incl y) := sorry


  -- definition ifin_of_nat_add (n x : ℕ)
  --   : Πy, ifin_of_nat n (x + y) = ifin_of_nat n x + ifin_of_nat n y
  -- | 0        := _
  -- | (succ k) := _


  theorem nat_of_ifin_of_nat (n k : ℕ) : nat_of_ifin (ifin_of_nat n k) = k % (succ n) :=
  begin
    apply fn_eq_mod: clear k,
    { apply nat_of_ifin_zero},
    { intro k, esimp [ifin_of_nat],
      cases (ifin_of_nat n k): intro H,
      { exfalso, exact lt.irrefl n H},
      { apply nat_of_ifin_succ'}},
    { intro k, esimp [ifin_of_nat],
      cases (ifin_of_nat n k): intro H,
      { apply nat_of_ifin_zero},
      { exfalso, exact nat_of_ifin_incl_neq _ H}},
  end

  -- theorem ifin_of_nat_of_ifin : Π{n : ℕ} (x : ifin (succ n)), ifin_of_nat n (nat_of_ifin x) = x
  -- | n (max n)  := _
  -- | n (incl x) := _

  -- TODO: prove theorems about these constructions.

  example (n : ℕ) : has_zero (ifin (n+6)) := _

  definition flatten {n : ℕ} (x : ℕ × ifin n) : ℕ := n * (pr1 x) + nat_of_ifin (pr2 x)
  definition unflatten (n : ℕ) (x : ℕ) : ℕ × ifin (succ n) :=
  (x / succ n, ifin_of_nat n x)

  theorem flatten_unflatten {n : ℕ} (x : ℕ) : flatten (unflatten n x) = x :=
  begin
    unfold [flatten, unflatten],
    refine _ ⬝ (eq_div_mul_add_mod x (succ n))⁻¹,
    rewrite [nat_of_ifin_of_nat, mul.comm]
  end

  theorem unflatten_flatten {n : ℕ} (x : ℕ × ifin (succ n)) : unflatten n (flatten x) = x :=
  begin
    cases x with m y, unfold [flatten, unflatten],
    apply prod_eq: esimp,
    { rewrite [add.comm, add_mul_div_self_left _ _ (!zero_lt_succ),
               div_eq_zero_of_lt (nat_of_ifin_lt y), zero_add]},
    { exact sorry}
  end

end ifin
