/- NOT FOR BLESSED REPOSITORY -/

open eq is_trunc nat sigma sigma.ops bool

/- private -/ inductive susp (A : Type) : Type :=
N {} : susp A,
S {} : susp A

definition N [reducible] := @susp.N
definition S [reducible] := @susp.S

axiom merid {A : Type} (a : A) : @N A = @S A

definition susp_rec {A : Type} {P : susp A → Type} (HN : P N) (HS : P S)
  (Hm : Πa, merid a ▹ HN = HS) : Πaa, P aa :=
susp.rec HN HS

definition susp_rec_on {A : Type} {P : susp A → Type} (aa : susp A) (HN : P N) (HS : P S)
  (Hm : Πa, merid a ▹ HN = HS) : P aa :=
susp_rec HN HS Hm aa

definition susp_rec_on' {A : Type} {P : Type} (aa : susp A) (HN : P) (HS : P)
  (Hm : A → HN = HS) : P :=
susp_rec_on aa HN HS (λa, !tr_constant ⬝ Hm a)

/- private -/ inductive my_colim {A : ℕ → Type} (f : Π⦃n⦄, A n → A (succ n)) : Type :=
inc : Π{n}, A n → my_colim f

definition inc [reducible] := @my_colim.inc

axiom inc_eq {A : ℕ → Type} (f : Π⦃n⦄, A n → A (succ n)) {n : ℕ} (a : A n) : inc f (f a) = inc f a

definition my_colim_rec {A : ℕ → Type} (f : Π⦃n⦄, A n → A (succ n))
  {P : my_colim f → Type} (Hinc : Π⦃n : ℕ⦄ (a : A n), P (inc f a))
  (Heq : Π(n : ℕ) (a : A n), inc_eq f a ▹ Hinc (f a) = Hinc a) : Πaa, P aa :=
my_colim.rec Hinc

definition my_colim_rec_on {A : ℕ → Type} (f : Π⦃n⦄, A n → A (succ n))
  {P : my_colim f → Type} (aa : my_colim f) (Hinc : Π⦃n : ℕ⦄ (a : A n), P (inc f a))
  (Heq : Π(n : ℕ) (a : A n), inc_eq f a ▹ Hinc (f a) = Hinc a) : P aa :=
my_colim_rec f Hinc Heq aa


private definition A [reducible] (n : ℕ) : Type₀ :=
nat.rec_on n bool (λn' X', susp X')

set_option pp.implicit true
private definition f [reducible] ⦃n : ℕ⦄ (a : A n) : A (n+1) :=
nat.rec_on n (λa', bool.rec_on a' N S)
             (λn' IH (a' : A (n'+1)), susp_rec_on' a' N S
               (λ(a'' : A n'), merid (IH a''))) a

definition Sinf [reducible] := @my_colim A f

definition c [reducible] : Sinf := inc f tt

private definition frep [reducible] {n : ℕ} (k : ℕ) (a : A n) : A (n+k) :=
nat.rec_on k a (λk' a', f a')

private definition frep_eq [reducible] {n : ℕ} (k : ℕ) (a : A n) : inc f (frep k a) = inc f a :=
nat.rec_on k idp (λk' p', !inc_eq ⬝ p')

definition eq_partial [reducible] {n : ℕ} (a a' : A n) : inc f a = inc f a' :=
calc
  inc f a = inc f (f a) : inc_eq
      ... = inc f (f a') : ap (inc f) (tr_eq a a')
      ... = inc f a' : inc_eq

definition eq_partial_eq''' {n : ℕ} (a a' : X)
  : (inc_eq f (f a))⁻¹ ⬝ ap (inc f) (tr_eq (f a) (f a')) ⬝ inc_eq f (f a') =
    ap (inc f) (tr_eq a a') :=
_


definition eq_partial_eq'' {n : ℕ} (a a' : X)
  : (inc_eq f (f a))⁻¹ ⬝ ap (inc f) (tr_eq (f a) (f a')) ⬝ inc_eq f (f a') =
    ap (inc f) (tr_eq a a') :=
_


definition eq_partial_eq' {n : ℕ} (a a' : A n)
  : (inc_eq f (f a))⁻¹ ⬝ ap (inc f) (tr_eq (f a) (f a')) ⬝ inc_eq f (f a') =
    ap (inc f) (tr_eq a a') :=
_

definition eq_partial_eq {n : ℕ} (a a' : A n)
  : eq_partial (f a) (f a') = !inc_eq ⬝ eq_partial a a' ⬝ !inc_eq⁻¹ :=
begin
 esimp {eq_partial},
end

--set_option pp.implicit true
definition eq_partial2 [reducible] {n k : ℕ} (b : A (n + k)) (a : A n) : inc f b = inc f a :=
!eq_partial ⬝ !frep_eq

definition eq_partial2_eq {n k : ℕ} (b : A (n + k)) (a : A n) : @eq_partial2 n (k+1) (f b) a =
  inc_eq f b ⬝ eq_partial2 b a :=
_


definition add_zero [reducible] (n : ℕ) : 0 + n = n :=
nat.rec_on n idp (λn p, ap succ p)

definition add_succ [reducible] (n k : ℕ) : succ n + k = succ (n + k) :=
nat.rec_on k idp (λn p, ap succ p)

definition add_comm [reducible] (n k : ℕ) : n + k = k + n :=
nat.rec_on n !add_zero (λn p, !add_succ ⬝ ap succ p)

definition eq_partial3 [reducible] {n k : ℕ} : Π(b : A (k + n)) (a : A n), inc f b = inc f a :=
add_comm n k ▹ @eq_partial2 n k

-- set_option pp.universes true
-- set_option pp.notation false
attribute succ [reducible]
definition lt.elim [reducible] {n m : ℕ} (H : n < m) : Σk, m = n + succ k :=
lt.rec_on H ⟨0,idp⟩ (λm' H' IH, ⟨succ IH.1, ap succ (IH.2 ⬝ by esimp)⟩)

definition my_nat_rec [reducible] {P : ℕ → ℕ → Type} (n m : ℕ) (H1 : Π(n k : ℕ), P n (n + k))
  (H2 : Π(n k : ℕ), P (n + k) n) : P n m :=
--nat.rec_on n _ (λn' IH P' m' H1' H2', _) P m H1 H2
sum.rec_on (lt.trichotomy n m) _ _


definition eq_partial4 [reducible] {m : ℕ} : Π{n : ℕ} (a : A n) (b : A m), inc f a = inc f b :=
begin
  apply (nat.rec_on m),
    {intros (n, a, b), exact (eq_partial3 a b)},
    {clear m, intros (m, IH, n),
      -- apply (nat.rec_on n),
      --   {intros (a, b), exact (eq_partial3 b a)⁻¹},
      --   {clear n, intros (n, IH', a, b), }}
    apply sorry

end
check @my_colim_rec_on

definition my_tr_eq1 [reducible] (b : my_tr) {n : ℕ} (a : A n) : inc f a = b :=
begin
  fapply (my_colim_rec_on f b),
    {clear b, intros (m, b), apply eq_partial4},
    {/-clear b,-/ intros (m, b'), },
end


definition my_tr_eq [reducible] (a : my_tr) : Π(b : my_tr), a = b :=
begin
  fapply (my_colim_rec_on f a),
    {clear a, intros (n, a, b), },
end
