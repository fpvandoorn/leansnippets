import hit.quotient types.W

open quotient Wtype

-- The definition of something similar to case of W-suspensions using type quotients.
-- The special case is the case where the second argument of "sup" has codomain W(A, B) instead of W(A, B, C, l, r)

namespace Wsusp
section
  parameters {A C : Type} {B : A → Type} (l r : C → A)
--  variables (a a' : A)

  local abbreviation D := W(a : A), B a

  inductive R : D → D → Type :=
  Rmk : Π(c : C) (t : B (l c) → D) (s : B (r c) → D), R (sup (l c) t) (sup (r c) s)

  parameter (B)
  definition Wsusp : Type := quotient R
  parameter {B}
  definition hsup (a : A) (t : B a → W a, B a) : Wsusp :=
  class_of R (sup a t)

  definition cell (c : C) (t : B (l c) → W a, B a) (s : B (r c) → W a, B a) : hsup (l c) t = hsup (r c) s :=
  eq_of_rel _ !R.Rmk

  -- protected definition rec [recursor] {P : Wsusp → Type} (Pt : Π(a : A), P (tr a))
  --   (Pe : Π(a a' : A), Pt a =[tr_eq a a'] Pt a') (x : Wsusp) : P x :=
  -- begin
  --   fapply (quotient.rec_on x),
  --   { intro a, apply Pt},
  --   { intro a a' H, cases H, apply Pe}
  -- end

end
end Wsusp
open Wsusp
