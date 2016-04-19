import hit.two_quotient

open two_quotient e_closure pi equiv eq is_equiv relation sigma function

namespace two_quotient

  section
  parameters {A : Type}
             (R : A → A → Type)
  local abbreviation T := e_closure R
  parameter  (Q : Π⦃a a'⦄, T a a' → T a a' → Type)
  variables ⦃a a' a'' : A⦄ {s : R a a'} {t t' : T a a'}

  /- non-dependent universal property -/

  definition two_quotient_arrow_fun {X : Type} (h : two_quotient R Q → X)
    : Σ(f : A → X) (e : Π⦃a a'⦄, R a a' → f a = f a'),
    Πa a' (t t' : T a a'), Q t t' → e_closure.elim e t = e_closure.elim e t' :=
  ⟨h ∘ incl0 R Q,
   λa a' r, ap h (incl1 R Q r),
   λa a' t t' q, (ap_e_closure_elim h _ t)⁻¹ ⬝ ap02 h (incl2 R Q q) ⬝ ap_e_closure_elim h _ t'⟩

  definition two_quotient_arrow_inv {X : Type}
    (v : Σ(f : A → X) (e : Π⦃a a'⦄, R a a' → f a = f a'),
           Π⦃a a'⦄ {t t' : T a a'}, Q t t' → e_closure.elim e t = e_closure.elim e t')
    (x : two_quotient R Q) : X :=
  begin
    cases v with f v, cases v with e g,
    induction x,
    { exact f a},
    { exact e s},
    { exact g q}
  end

  definition two_quotient_arrow_equiv (X : Type) : (two_quotient R Q → X) ≃
    Σ(f : A → X) (e : Π⦃a a'⦄, R a a' → f a = f a'),
      Πa a' (t t' : T a a'), Q t t' → e_closure.elim e t = e_closure.elim e t' :=
  begin
    apply equiv.MK two_quotient_arrow_fun two_quotient_arrow_inv,
    { intro v, cases v with f v, cases v with e g, fapply sigma_eq: esimp, apply pathover_idp_of_eq,
      -- exact sorry
      fapply sigma_eq: esimp,
      { apply eq_of_homotopy3, intro a a' r, apply elim_incl1},
      { apply pi_pathover_constant, intro a,
        apply pi_pathover_constant, intro a',
        apply pi_pathover_constant, intro t,
        apply pi_pathover_constant, intro t',
        apply pi_pathover_constant, intro q,
        apply eq_pathover, refine _ ⬝pv !top_deg_square, exact sorry}},
    { intro f, apply eq_of_homotopy, intro z, induction z,
      { reflexivity},
      { apply eq_pathover, apply hdeg_square, apply elim_incl1},
      { exact sorry}}
  end
  end
end two_quotient
