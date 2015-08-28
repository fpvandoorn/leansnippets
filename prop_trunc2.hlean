-- more things related to the propositional truncation file

import .propositional_truncation cubical.squareover

open one_step_tr equiv eq sigma

definition one_step_tr_up (A B : Type)
  : (one_step_tr A → B) ≃ Σ(f : A → B), Π(x y : A), f x = f y :=
begin
  fapply equiv.MK,
  { intro f, fconstructor, intro a, exact f (tr a), intros, exact ap f !tr_eq},
  { intro v a, induction v with f p, induction a, exact f a, apply p},
  { intro v, induction v with f p, esimp, apply ap (sigma.mk _), apply eq_of_homotopy2, intro a a',
    apply elim_tr_eq},
  { intro f, esimp, apply eq_of_homotopy, intro a, induction a,
      reflexivity,
      apply eq_pathover, apply hdeg_square, rewrite [▸*,elim_tr_eq]},
end
exit
definition one_step_tr_dup {A : Type} (B : one_step_tr A → Type)
  : (Π(x : one_step_tr A), B x) ≃ Σ(f : Πa, B (tr a)), Π(x y : A), f x =[tr_eq x y] f y :=
begin
  fapply equiv.MK,
  { intro f, fconstructor, intro a, exact f (tr a), intros, exact apdo f !tr_eq},
  { intro v a, induction v with f p, induction a, exact f a, apply p},
  { intro v, induction v with f p, esimp, apply ap (sigma.mk _), apply eq_of_homotopy2, intro a a',
    apply rec_tr_eq},
  { intro f, esimp, apply eq_of_homotopy, intro a, induction a,
      reflexivity,
      apply eq_pathover, apply hdeg_square, rewrite [▸*,elim_tr_eq]},
end

definition two_step_tr_up (A B : Type)
  : (one_step_tr (one_step_tr A) → B) ≃ Σ(f : A → B) (p : Π(x y : A), f x = f y), sorry :=
begin
  fapply equiv.MK,
  { intro f, fconstructor,
      intro a, exact f (tr (tr a)),
      fconstructor, intros, exact ap f !tr_eq, exact sorry},
  { intro v a, induction v with f w, induction w with p s, induction a,
    { induction a, exact f a, apply p},
    { esimp, }},
  { },
  { },
end
