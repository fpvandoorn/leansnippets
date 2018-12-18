import .susp_set types.unit

open susp eq is_trunc

definition is_contr_loop [instance] {A : Type} [is_set A] (a : A) : is_contr (a = a) :=
is_contr_of_inhabited_prop idp

namespace susp

  universe variable u
  variable {P : Prop.{u}}

  definition code_K {x y : susp P}  (p : x = y) : trunctype.{u} (-2) :=
  begin
    induction x using susp.rec_prop: induction y using susp.rec_prop,
    { exact trunctype.mk (p = idp) _ },
    { exact trunctype.mk (lift unit) _ },
    { exact trunctype.mk (lift unit) _ },
    { exact trunctype.mk (p = idp) _ },
  end

  definition axiom_K {x y : susp P}  (p : x = y) : code_K p :=
  begin
    induction p, induction x using susp.rec_prop,
    exact idp, exact idp
  end

  definition easy_code_K {x : susp P}  (p : north = x) : trunctype.{u} (-2) :=
  begin
    induction x using susp.rec_prop,
    { exact trunctype.mk (p = idp) _ },
    { exact trunctype.mk (lift unit) _ }
  end

  definition easy_axiom_K' {x : susp P}  (p : north = x) : easy_code_K p :=
  begin
    induction p, exact idp
  end

  definition easy_axiom_K (p : north = north :> susp P) : p = idp :=
  easy_axiom_K' p

  definition easy_axiom_K_idp : easy_axiom_K idp = idpath (idpath (@north P)) :=
  idp

end susp

namespace interval

  definition interval.rec_prop [unfold 5] [recursor 5] {P : interval → Type} [Πx, is_prop (P x)]
    (h₀ : P zero) (h₁ : P one) (x : interval) : P x :=
  interval.rec h₀ h₁ !is_prop.elimo x

  definition code_K {x y : interval}  (p : x = y) : trunctype.{0} (-2) :=
  begin
    induction x using interval.rec_prop: induction y using interval.rec_prop,
    { exact trunctype.mk (p = idp) _ },
    { exact trunctype.mk (lift unit) _ },
    { exact trunctype.mk (lift unit) _ },
    { exact trunctype.mk (p = idp) _ },
  end


end interval
