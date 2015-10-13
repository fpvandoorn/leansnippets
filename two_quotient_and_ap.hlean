import hit.two_quotient homotopy.interval

open two_quotient sum unit interval e_closure eq function

namespace test

  definition A := interval + unit

  inductive R : A → A → Type :=
  | Rmk0 : R (inl zero) (inr star)
  | Rmk1 : R (inl one) (inr star)
  open R


  -- definition torus_R (x y : unit) := bool
  -- local infix `⬝r`:75 := @e_closure.trans unit torus_R star star star
  -- local postfix `⁻¹ʳ`:(max+10) := @e_closure.symm unit torus_R star star
  -- local notation `[`:max a `]`:0 := @e_closure.of_rel unit torus_R star star a

  inductive Q : Π⦃x y : A⦄, e_closure R x y → e_closure R x y → Type :=
  | Qmk : Q (ap inl seg ▸ [Rmk0]) [Rmk1]
  open Q
  definition triangle := two_quotient R Q
  definition x0 : triangle := incl0 R Q (inl zero)
  definition x1 : triangle := incl0 R Q (inl one)
  definition x2 : triangle := incl0 R Q (inr star)
  definition p01 : x0 = x1 := ap (incl0 R Q) (ap inl seg)
  definition p02 : x0 = x2 := incl1 R Q Rmk0
  definition p12 : x1 = x2 := incl1 R Q Rmk1

  open relation

  definition fill : p01⁻¹ ⬝ p02 = p12 :=
  !e_closure.transport_left⁻¹ ⬝ incl2 R Q Qmk

  definition elim (P : Type) (P0 : A → P) (P10 : P0 (inl zero) = P0 (inr star))
    (P11 : P0 (inl one) = P0 (inr star)) (P2 : (ap P0 (ap inl seg))⁻¹ ⬝ P10 = P11)
    (y : triangle) : P :=
  begin
    induction y,
    { exact P0 a},
    { induction s,
      { exact P10},
      { exact P11}},
    { induction q, esimp, exact !e_closure.transport_left ⬝ P2}
  end

end test
