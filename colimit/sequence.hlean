/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Egbert Rijke
-/

import types.nat .move_to_lib

open nat eq equiv sigma sigma.ops is_equiv

namespace seq_colim

  definition seq_diagram [class] (A : ℕ → Type) : Type := Π⦃n⦄, A n → A (succ n)
  -- structure seq_diagram [class] (A : ℕ → Type) : Type :=
  -- (f : Πn, A n → A (succ n))

  structure Seq_diagram : Type :=
    (carrier : ℕ → Type)
    (struct : seq_diagram carrier)

  definition is_equiseq [class] {A : ℕ → Type} (f : seq_diagram A) : Type := forall (n : ℕ), is_equiv (@f n)

  structure Equi_seq : Type :=
    (carrier : ℕ → Type)
    (maps : seq_diagram carrier)
    (prop : is_equiseq maps)

  definition is_equiv_of_equiseq [instance] {A : ℕ → Type} (f : seq_diagram A) [H : is_equiseq f] : forall (n : ℕ), is_equiv (@f n) :=
    H

  protected abbreviation Mk [constructor] := Seq_diagram.mk
  attribute Seq_diagram.carrier [coercion]
  attribute Seq_diagram.struct [instance] [priority 10000] [coercion]

  variables {A : ℕ → Type} [f : seq_diagram A]
  variables {n : ℕ} (a : A n)
  include f

  definition rep [reducible] (k : ℕ) (a : A n) : A (n + k) :=
  by induction k with k x;exact a;exact f x

  definition rep_f (k : ℕ) (a : A n) : rep k (f a) =[succ_add n k] rep (succ k) a :=
  begin
    induction k with k IH,
    { esimp [succ_add], constructor},
    { esimp [succ_add,add_succ], apply pathover_ap,
      exact apo f IH}
  end

  definition req_equiseq_back [H : is_equiseq f] (k : ℕ) (a : A (n + k)) : A n :=
  begin
    induction k with k g,
    exact a,
    exact g ((@f (n + k))⁻¹ a),
  end

  definition req_equiseq_is_equiv [H : is_equiseq f] (k : ℕ) : is_equiv (λ (a : A n), rep k a) :=
  begin
    fapply adjointify,
    exact (λ (a : A (n + k)), req_equiseq_back k a),
    induction k with k IH: intro b,
    exact rfl,
    unfold rep,
    unfold req_equiseq_back,
    fold [rep k (req_equiseq_back k ((@f (n+k))⁻¹ b))],
    refine _ ⬝ _,
    exact (@f (n+k)) ((@f (n+k))⁻¹ b),
    exact (ap (@f (n+k)) (IH ((@f (n+k))⁻¹ b))),
    apply right_inv (@f _),
    induction k with k IH: intro b,
    exact rfl,
    unfold req_equiseq_back,
    unfold rep,
    fold [rep k b],
    refine _ ⬝ _,
    exact (req_equiseq_back k (rep k b)),
    exact (ap (req_equiseq_back k) (@left_inv _ _ (@f (n+k)) _ (rep k b))),
    exact IH b,
  end

  definition rep_rep (k l : ℕ) (a : A n) : rep k (rep l a) =[my.add_add n l k] rep (k + l) a :=
  begin
    induction l with l IH,
    { esimp [rep, my.add_add, add], constructor},
    { exact sorry
      -- rewrite [▸rep k (f (rep l a)) =[ succ_add (n + l) k ⬝ ap succ (my.add_add n l k)]
      --           f (rep (k + l) a)],
      -- refine rep_f k (rep l a) ⬝o _,
      -- rewrite [▸f (rep k (rep l a)) =[ ap succ (my.add_add n l k) ] f (rep (k + l) a)],
      -- apply pathover_ap, exact apo f IH
      }
  end

  definition f_rep (k : ℕ) (a : A n) : f (rep k a) = rep (succ k) a := idp

  variable (A)
  definition shift_diag [instance] [unfold-full] : seq_diagram (λn, A (succ n)) :=
  λn a, f a

  definition kshift_diag [instance] [unfold-full] [priority 800] (k : ℕ)
    : seq_diagram (λn, A (k + n)) :=
  λn a, f a

  definition kshift_diag' [instance] [unfold-full] [priority 800] (k : ℕ)
    : seq_diagram (λn, A (n + k)) :=
  λn a, !succ_add⁻¹ ▸ f a

  definition arrow_left_diag [instance] [unfold-full] (X : Type)
    : seq_diagram (λn, X → A n) :=
  λn g x, f (g x)

  variable {A}
  section over
  variable (P : Π⦃n⦄, A n → Type)

  definition seq_diagram_over [class] : Type := Π⦃n⦄ {a : A n}, P a → P (f a)

  variable [g : seq_diagram_over P]
  include g
  definition seq_diagram_of_over [instance] [unfold-full] {n : ℕ} (a : A n)
    : seq_diagram (λk, P (rep k a)) :=
  λk p, g p

  definition seq_diagram_sigma [instance] : seq_diagram (λn, Σ(x : A n), P x) :=
  λn v, ⟨f v.1, g v.2⟩

  theorem rep_f_equiv [constructor] (k : ℕ) : P (rep (succ k) a) ≃ P (rep k (f a)) :=
  equiv_of_eq (apo011 P _ (rep_f k a)⁻¹ᵒ)

  theorem rep_rep_equiv [constructor] (k l : ℕ) : P (rep (k + l) a) ≃ P (rep k (rep l a)) :=
  equiv_of_eq (apo011 P _ (rep_rep k l a)⁻¹ᵒ)

  end over

end seq_colim
