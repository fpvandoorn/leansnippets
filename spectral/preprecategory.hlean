-- Author: Floris van Doorn

import types.prod

universe variables u v
open eq pointed prod

structure pretwocategory [class] (A : Type.{u}) : Type :=
mk :: (hom : A → A → Type.{v})
      (hom2 : Π⦃a a'⦄, hom a a' → hom a a' → Type.{v})

variables {X Y : Type} {A B : Type} [pretwocategory A] [pretwocategory B]

open pretwocategory
definition pretwocategory_Type [instance] : pretwocategory Type.{u} :=
pretwocategory.mk (λX Y, X → Y) (λX Y f g, f ~ g)

definition pretwocategory_pType [instance] : pretwocategory Type* :=
pretwocategory.mk (λX Y, X →* Y) (λX Y f g, f ~* g)

-- definition pretwocategory_pi [instance] (A : X → Type) [Πx, pretwocategory (A x)] :
--   pretwocategory (Πx, A x) :=
-- pretwocategory.mk (λf f', Πx, hom (f x) (f' x)) (λf f' h h', Πx, hom2 (h x) (h' x))

definition pretwocategory_arrow (X A : Type) [pretwocategory A] :
  pretwocategory (X → A) :=
pretwocategory.mk (λf f', Πx, hom (f x) (f' x)) (λf f' h h', Πx, hom2 (h x) (h' x))

definition pretwocategory_hom (a a' : A) : pretwocategory (hom a a') :=
pretwocategory.mk (λf f', hom2 f f') (λf f' p q, p = q)

-- definition is_hom (X : Type) : Type :=
-- mk :: (A : Type) (hA : pretwocategory A)

definition my_id [unfold_full] (X : Type) : Type := X
notation ↑ := my_id

definition pretwocategory_variable [instance] (X : Type) : pretwocategory (↑X) :=
pretwocategory.mk (λa a', a = a') (λa a' p q, p = q)

-- definition foo4 (F : functorial (Type* → Type* → Type*)) (X X' Y Y' : Type*)
--   (f : X →* X') (g : Y →* Y') : F X Y →* F X' Y' :=
-- begin  end

structure functor_type [class] (X : Type) : Type :=
mk :: (cond : X → X → Type)

structure dfunctor_type [class] (Y : A → Type) : Type :=
mk :: (cond : Π⦃x₁ x₂ : A⦄ (f : hom x₁ x₂), Y x₁ → Y x₂ → Type)

variables {α β : Type} [functor_type α] [functor_type β]

structure functorial [class] (h : α) : Type :=
mk :: (struct : functor_type.cond h h)

definition functor_type_of_pretwocategory [instance] (A : Type) [pretwocategory A] : functor_type A :=
functor_type.mk hom

definition functor_type_arrow [instance] (A α : Type) [pretwocategory A] [functor_type α] :
  functor_type (A → α) :=
functor_type.mk (λ(h h' : A → α), Π⦃a a' : A⦄ (f : hom a a'), functor_type.cond (h a) (h' a'))

definition functor_type_pi [instance] (α : A → Type) [dfunctor_type α] :
  functor_type (Πa, α a) :=
functor_type.mk (λ(h h' : Πa, α a), Π⦃a a' : A⦄ (f : hom a a'), dfunctor_type.cond f (h a) (h' a'))

definition dfunctor_type_dependent_type [instance] : dfunctor_type (λ(A : Type), A → Type) :=
dfunctor_type.mk (λ(A A' : Type) (f : A → A') (B : A → Type) (B' : A' → Type),
  Π(a : A), B a → B' (f a))

-- definition dfunctor_type_arrow [instance] (α β : A → Type) [dfunctor_type β] :
--   dfunctor_type (λa, α a → β a) :=
-- dfunctor_type.mk (λ(a a' : A) (h : α a → β a) (h' : α a' → β a'), Π⦃x : α a⦄ ⦃x' : α a'⦄
--   (f : )

-- -- structure functor [class] (h : X) : Type :=
-- -- mk :: (on_hom : Π⦃a a' : A⦄ (f : hom a a'), hom (h a) (h a'))

-- variables {F G : A → B} [functor F] [functor G]

-- structure nt [class] (F G : A → B) [functor F] [functor G] : Type :=
-- mk :: (on_hom : Πa, hom (F a) (G a))


exit
-- set_option trace.class_instances true
set_option pp.universes true
-- definition foo1 : pretwocategory (A → Type.{u}) := _
definition foo2 : pretwocategory (↑A) := _
--definition foo3 : pretwocategory A := _ -- should fail
definition foo5 : functor_type (↑X → Type) := _
definition foo6 : functor_type (Π(X : Type.{u}), X → Type.{u}) := _
definition foo7 : functor_type (Π(X : Type), X → Type) := _
definition foo8 : functor_type (Π(X : Type), (X → Type) → Type) := _

definition foo13 : functorial (λ(A : Type) (a : A), A) :=
begin
  constructor, intro A B f a a', exact f a
end

definition foo10 : functorial option :=
begin
  constructor,
  esimp [functor_type_arrow, functor_type_of_pretwocategory],
  intro X X' f,
  intro x, exact sorry
end

definition foo11 : functorial prod :=
begin
  constructor,
  esimp [functor_type_arrow, functor_type_of_pretwocategory],
  intro X X' f Y Y' g, exact f ×→ g
end

set_option trace.class_instances true


definition foo12 : functorial.{(max (u+1) (v+1)) (max u v)} @sigma.{u v} :=
begin
  constructor,
  esimp [functor_type_arrow, functor_type_of_pretwocategory],
  intro X X' f Y Y' g, exact f ×→ g
end
