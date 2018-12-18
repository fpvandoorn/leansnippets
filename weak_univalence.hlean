
import types.equiv
open eq is_equiv equiv is_trunc trunctype function

axiom weak_prop_ua {A B : Type} [is_prop A] [is_prop B] : A ≃ B → A = B :> Type

axiom is_equiv_of_imp_is_equiv {A B : Type} (f : A → B) (H : B → is_equiv f) : is_equiv f
--set_option pp.all true
--set_option pp.implicit true
theorem prop_ua {A B : Type} [HA : is_prop A] [HB : is_prop B] : is_equiv (@equiv_of_eq A B) :=
begin
  fapply adjointify,
  exact (λe, weak_prop_ua e ⬝ (weak_prop_ua erfl)⁻¹),
  { intro e, apply equiv_eq, intro a, !is_prop.elim },
  { intro p, induction p, have HA = HB, from !is_prop.elim, induction this,
    refine !con.right_inv }
end

print axioms is_prop_is_trunc
print axioms equiv_eq
print axioms is_equiv_of_imp_is_equiv
