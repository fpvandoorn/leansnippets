-- more things related to the propositional truncation file

import .propositional_truncation cubical.squareover

open one_step_tr equiv eq sigma function




exit

attribute one_step_tr.tr [constructor]
attribute one_step_tr.rec one_step_tr.elim [recursor 5]


definition universal_property2 (A B : Type) : (one_step_tr (one_step_tr A) → B) ≃
  Σ(f : A → B) (p : Πa b, f a = f b), Πa b c, p a b ⬝ p b c = p a c :=
begin
  fapply equiv.MK,
  { intro f, fconstructor: try fconstructor,
    { intro a, exact f (tr (tr a))},
    { intro a b, refine ap (f ∘ tr) !tr_eq},
    { intro a b c, exact sorry}},
  { intro v y, induction v with f w, induction w with p q,
    induction y with x x x',
    { induction x with a a a',
      { exact f a},
      { apply p}},
    { esimp, induction x with a a a': induction x' with b b b',
      { apply p},
      { apply eq_pathover, rewrite [elim_tr_eq, ap_constant], apply square_of_eq,
        exact !q ⬝ !idp_con⁻¹},
      { esimp, unfold [one_step_tr.rec], apply eq_pathover, rewrite [elim_tr_eq,ap_constant],
        apply square_of_eq, exact !q⁻¹},
      { }}},
  { },
  { },
end


definition one_step_tr_dup {A : Type} (B : one_step_tr A → Type)
  : (Π(x : one_step_tr A), B x) ≃ Σ(f : Πa, B (tr a)), Π(x y : A), f x =[tr_eq x y] f y :=
begin
  fapply equiv.MK,
  { intro f, fconstructor, intro a, exact f (tr a), intros, exact apd f !tr_eq},
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
