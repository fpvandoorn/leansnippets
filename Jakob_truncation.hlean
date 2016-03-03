
import types.pi

open eq is_trunc pi equiv sigma.ops sigma

definition prop_truncate (A : Type) : Type :=
Π (P : Type), (is_prop P) → (A → P) → P

namespace prop_truncate

  notation `∥` A `∥` := prop_truncate A

  definition is_prop_of_prop_truncate [instance] (A : Type) : is_prop ∥ A ∥ :=
  begin
    apply is_trunc_pi,
  end

  definition prop_abs {A : Type} (a : A) : ∥ A ∥ :=
  (λ P H f, f a)

  protected definition rec [reducible] {A B : Type} [HB : is_prop B] (f : A → B) (aa : ∥ A ∥) : B :=
  aa B HB f

  protected definition rec_on [reducible] {A : Type} (aa : ∥ A ∥) {B : Type} [HB : is_prop B] (f : A → B) : B :=
  aa B HB f

  definition equiv_lift (A : Type) : A ≃ lift A :=
  begin
    fapply equiv.mk,
      exact (@lift.up A),
    fapply is_equiv.adjointify,
        exact (@lift.down A),
      intro a, apply (lift.rec_on a), intro down, apply idp,
    intro a, apply idp,
  end

  universe variable l
  definition equiv_prop_truncate (A : Type.{l}) [HA : is_prop A] : A ≃ prop_truncate.{l l+1} A :=
  begin
    have HlA : is_prop (lift A),
    begin apply is_trunc_equiv_closed, apply equiv_lift end,
    apply equiv.trans,
      apply equiv_lift.{l l+1},
    fapply equiv.mk,
      intro la, eapply (lift.rec_on la), exact (@prop_abs.{l l+1} A),
    fapply is_equiv.adjointify,
        intro aa, apply (aa (lift A) HlA (λ x, lift.up x)),
      intros, apply (@is_prop.elim (prop_truncate.{l l+1} A) (is_prop_of_prop_truncate.{l l+1} A)),
    intros, apply is_prop.elim,
  end

  definition unique_choice {A : Type} (P : A → Type) [HP : Π x, is_prop (P x)] (choice : Π x, ∥ P x ∥) :
    Π x, P x :=
  (λ x, (is_equiv.inv (equiv.to_fun (equiv_prop_truncate (P x)))) (choice x))

end prop_truncate
