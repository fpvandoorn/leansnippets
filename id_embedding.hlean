import function

open is_equiv function eq equiv

exit
/- email from Martin Escardo, nov 25. Try to prove that `Id_X` for all X without assumptions. Seems to fail -/
definition eq_cast {X A : Type} {E : X → A → Type} {x x' : X} {a a' : A} (p : E x ~ E x') (b' : E x' a') :
  begin note z := cast (p a')⁻¹ b' end = p a' :=
_

print apd10_ap
definition is_embedding_id (A : Type) : is_embedding (@eq A) :=
begin
  intro a₁ a₂, fapply adjointify,
  { intro p, exact cast (apd10 p a₂)⁻¹ (idpath a₂) },
  { intro p, apply inj !eq_equiv_homotopy,
    esimp [eq_equiv_homotopy], refine apd10_ap eq _ ⬝ _,
    generalize apd10 p, clear p, intro q,
    apply eq_of_homotopy, intro a,
},
  { intro q, induction q, reflexivity }
end
