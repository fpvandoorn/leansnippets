import classical

open set

section
structure foo.{l} : Type.{l+1} :=
(elim : Type.{l} → Type.{l})
end

structure topology [class] (X : Type) : Type :=
  (is_open : set X → Prop)
  (empty : is_open (λx, false))
  (full : is_open (λx, true))
  (union : Π(P : set X → Prop), (Πf, is_open f) → is_open (λx, ∃f, f x ∧ P f))
  (intersection : Πf g, is_open f → is_open g → is_open (λx, f x ∧ g x))

namespace topology
  variables (X Y : Type) [τ : topology X] [σ : topology Y]
  include τ
  set_option pp.universes true
  theorem foo : is_open (λ(x : X), false) := !empty

  -- definition union2 (P : (X → Prop) → Prop) (H : ΠO, P O → is_open O) :=
  -- union (λO : subtype P, subtype.elt_of O)
  definition interior (A : X → Prop) :=
  union (λB : X → Prop, is_open B ∧ B ⊆ A)

  include σ

  definition continuous (f : X → Y) :=
  ∀(B : set Y), is_open B → is_open (λx : X, f x ∈ B)

end topology

-- structure topology2 [class] (X : Type) (Y : Type) :=
--   (element : X → Y → Prop)
--   (extensionality : Πy1 y2, (Πx, element x y1 ↔ element x y2) → y1 = y2)
--   (empty : Y)
--   (is_empty : Πx, ¬element x empty)
--   (full : Y)
--   (is_full : Πx, element x full)
--   (union : Π{A : Type}, (A → Y) → Y)
--   (is_union : Πx A (F : A → Y), element x (union F) ↔ ∃a, element x (F a))
--   (intersection : Y → Y → Y)
--   (is_intersection : Πx O1 O2, element x (intersection O1 O2) ↔ element x O1 ∧ element x O2)

-- namespace topology2
--   variables (X Y : Type₊) (τ : topology2 X Y)
--   include τ
--   infix ∈ := element
--   notation 0 := empty
--   notation 1 := full
--   check @union
--   definition union2 (P : Y → Prop) := @union X _ τ _ (λO : subtype P, subtype.elt_of O)
--   set_option pp.universes true
--   check @subtype
--   definition interior (f : X → Prop) :=
--   union (λP : Σ(g : A), ,
-- end topology2
