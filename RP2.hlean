import hit.two_quotient

open eq unit relation is_equiv equiv function bool pi is_trunc trunc

section
  parameters {A : Type}
             {R : A → A → Type}
  local abbreviation T := e_closure R

  variables ⦃a a' a'' : A⦄ {s : R a a'} {r : T a a} {B C : Type}
            (S : B → B → Type) (S' : C → C → Type) [is_equivalence S] [is_equivalence S']

  protected definition e_closure.elim_rel [unfold 10] {f : A → B}
    (e : Π⦃a a' : A⦄, R a a' → S (f a) (f a')) (t : T a a') : S (f a) (f a') :=
  begin
    induction t with a a' r a a' pp a a' r IH a a' a'' r r' IH₁ IH₂,
      exact e r,
      exact pp ▸ rel_refl S (f a),
      exact rel_symm S IH,
      exact rel_trans S IH₁ IH₂
  end

  definition is_equivalence_equiv [constructor] [instance] : is_equivalence equiv :=
  is_equivalence.mk (λA, erfl) (λA B, equiv.symm) (λA B C, equiv.trans)

  definition is_equivalence_eq [constructor] [instance] (A : Type) : is_equivalence (@eq A) :=
  is_equivalence.mk idpath (λa b, inverse) (λa b c, concat)

  definition elim_rel_eq {f : A → B} (e : Π⦃a a' : A⦄, R a a' → f a = f a') (t : T a a') :
    e_closure.elim e t = e_closure.elim_rel eq e t :=
  by induction t: reflexivity

  definition ap_e_closure_elim [unfold 10] {B C : Type} {f : A → B} (g : B → C)
    (e : Π⦃a a' : A⦄, R a a' → f a = f a') (t : T a a')
    : ap g (e_closure.elim e t) = e_closure.elim (λa a' r, ap g (e r)) t :=
  ap_e_closure_elim_h e (λa a' s, idp) t

  definition ap_elim_rel {f : A → B} (e : Π⦃a a' : A⦄, R a a' → S (f a) (f a'))
    {g : B → C} (e2 : Π⦃b b' : B⦄, S b b' → S' (g b) (g b'))
    (e2r : Π(b : B), e2 (rel_refl S b) = rel_refl S' (g b))
    (e2s : Π⦃b b' : B⦄ (s : S b b'), e2 (rel_symm S s) = rel_symm S' (e2 s))
    (e2t : Π⦃b₁ b₂ b₃ : B⦄ (s : S b₁ b₂) (s' : S b₂ b₃), e2 (rel_trans S s s')
      = rel_trans S' (e2 s) (e2 s'))
    (t : T a a') :
    e2 (e_closure.elim_rel S e t) = e_closure.elim_rel S' (λa a' r, e2 (e r)) t :=
  begin
    induction t with a a' r a a' pp a a' r IH a a' a'' r r' IH₁ IH₂,
      reflexivity,
      induction pp, apply e2r,
      exact !e2s ⬝ ap (λs, rel_symm S' s) IH,
      exact !e2t ⬝ ap011 (λs s', rel_trans S' s s') IH₁ IH₂,
  end

end

  local attribute rel_refl rel_symm rel_trans [unfold 3]
  local attribute is_equivalence.to_is_reflexive is_equivalence.to_is_transitive
            is_equivalence.to_is_symmetric [constructor]

namespace two_quotient
  section
  open e_closure
  parameters {A : Type}
             (R : A → A → Type)
  local abbreviation T := e_closure R -- the (type-valued) equivalence closure of R
  parameter  (Q : Π⦃a a'⦄, T a a' → T a a' → Type)

  protected definition elim_type (P0 : A → Type)
    (P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a ≃ P0 a')
    (P2 : Π⦃a a' : A⦄ ⦃t t' : T a a'⦄ (q : Q t t'),
      e_closure.elim_rel equiv P1 t ~ e_closure.elim_rel equiv P1 t')
    : two_quotient R Q → Type :=
  two_quotient.elim P0 (λa a' r, ua (P1 r))
    abstract begin
      intros, rewrite [+elim_rel_eq],
      do 2 rewrite [-ap_elim_rel equiv eq P1 (λb b', ua) ua_refl @ua_symm @ua_trans],
      apply ap ua, apply equiv_eq, exact P2 q
    end end

  protected definition elim_type_on [reducible] (P0 : A → Type) (x : two_quotient R Q)
    (P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a ≃ P0 a')
    (P2 : Π⦃a a' : A⦄ ⦃t t' : T a a'⦄ (q : Q t t'),
      e_closure.elim_rel equiv P1 t ~ e_closure.elim_rel equiv P1 t') : Type :=
  elim_type P0 P1 P2 x

  theorem elim_type_incl1 {P0 : A → Type}
    {P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a ≃ P0 a'}
    (P2 : Π⦃a a' : A⦄ ⦃t t' : T a a'⦄ (q : Q t t'),
      e_closure.elim_rel equiv P1 t ~ e_closure.elim_rel equiv P1 t')
    ⦃a a' : A⦄ (s : R a a')
    : transport (elim_type P0 P1 P2) (incl1 R Q s) = P1 s :=
  by rewrite [tr_eq_cast_ap_fn,↑two_quotient.elim_type,elim_incl1]; apply cast_ua_fn

  theorem elim_type_inclt {P0 : A → Type}
    {P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a ≃ P0 a'}
    (P2 : Π⦃a a' : A⦄ ⦃t t' : T a a'⦄ (q : Q t t'),
      e_closure.elim_rel equiv P1 t ~ e_closure.elim_rel equiv P1 t')
    ⦃a a' : A⦄ (t : T a a') : transport (elim_type P0 P1 P2) (inclt R Q t) =
    e_closure.elim_rel equiv P1 t :=
  begin
    rewrite [tr_eq_cast_ap_fn,↑two_quotient.elim_type,elim_inclt,
             elim_rel_eq, -ap_elim_rel equiv eq P1 (λb b', ua) ua_refl @ua_symm @ua_trans],
    apply cast_ua_fn,
  end

  -- theorem elim_type_incl2 {P0 : A → Type}
  --   {P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a ≃ P0 a'}
  --   (P2 : Π⦃a a' : A⦄ ⦃t t' : T a a'⦄ (q : Q t t'),
  --     e_closure.elim_rel equiv P1 t ~ e_closure.elim_rel equiv P1 t')
  --   ⦃a a' : A⦄ ⦃t t' : T a a'⦄ (q : Q t t')
  --   : square (ap02 (elim_type P0 P1 P2) (incl2 q)) (P2 q) (elim_inclt P2 t) (elim_inclt P2 t') :=
  -- begin

  -- end
  end
end two_quotient
open two_quotient
attribute two_quotient.elim_type [unfold 7]
attribute two_quotient.elim_type_on [unfold 4]

namespace RP2
section
  open e_closure
  definition RP2_R [reducible] (x y : unit) : Type₀ := unit
  local infix `⬝r`:75 := @e_closure.trans unit RP2_R star star star
  inductive RP2_Q : Π⦃x y : unit⦄, e_closure RP2_R x y → e_closure RP2_R x y → Type₀ :=
  | Qmk : RP2_Q ([⋆] ⬝r [⋆]) rfl


  definition RP2 [reducible] : Type₀ := two_quotient RP2_R RP2_Q
  definition base : RP2 := incl0 _ _ ⋆
  definition loop : base = base := incl1 _ _ ⋆
  definition surf : loop ⬝ loop = idp := incl2 _ _ RP2_Q.Qmk

  protected definition rec {P : RP2 → Type} (Pb : P base) (Pl : Pb =[loop] Pb)
    (Ps : change_path surf (Pl ⬝o Pl) = idpo) (x : RP2) : P x :=
  begin
    induction x,
    { induction a, exact Pb},
    { induction s, induction a, induction a', exact Pl},
    { induction q, esimp, exact Ps},
  end

  protected definition rec_on [reducible] {P : RP2 → Type} (x : RP2) (Pb : P base)
    (Pl : Pb =[loop] Pb) (Ps : change_path surf (Pl ⬝o Pl) = idpo) : P x :=
  RP2.rec Pb Pl Ps x

  theorem rec_loop {P : RP2 → Type} {Pb : P base} {Pl : Pb =[loop] Pb}
    (Ps : change_path surf (Pl ⬝o Pl) = idpo)
    : apd (RP2.rec Pb Pl Ps) loop = Pl :=
  !rec_incl1

  protected definition elim {P : Type} (Pb : P) (Pl : Pb = Pb)
    (Ps : Pl ⬝ Pl = idp) (x : RP2) : P :=
  begin
    induction x,
    { exact Pb},
    { exact Pl},
    { induction q, exact Ps},
  end

  protected definition elim_on [reducible] {P : Type} (x : RP2) (Pb : P) (Pl : Pb = Pb)
    (Ps : Pl ⬝ Pl = idp) : P :=
  RP2.elim Pb Pl Ps x

  definition elim_loop {P : Type} {Pb : P} {Pl : Pb = Pb}
    (Ps : Pl ⬝ Pl = idp) : ap (RP2.elim Pb Pl Ps) loop = Pl :=
  !elim_incl1

  theorem elim_surf {P : Type} {Pb : P} {Pl : Pb = Pb}
    (Ps : Pl ⬝ Pl = idp)
    : square (ap02 (RP2.elim Pb Pl Ps) surf) Ps (!ap_con ⬝ (elim_loop Ps ◾ elim_loop Ps)) idp :=
  !elim_incl2

  protected definition elim_type.{u} (Pb : Type.{u}) (Pl : Pb ≃ Pb) (Ps : Pl ∘ Pl ~ id)
    : RP2 → Type.{u} :=
  begin
    fapply two_quotient.elim_type,
    { intro u, exact Pb},
    { intro u u' r, exact Pl},
    { intro u u' r r' q, induction q, exact Ps}
  end

  protected definition elim_type_on [reducible] (x : RP2) (Pb : Type) (Pl : Pb ≃ Pb)
    (Ps : Pl ∘ Pl ~ id) : Type :=
  RP2.elim_type Pb Pl Ps x

  theorem elim_type_loop (x : RP2) (Pb : Type) (Pl : Pb ≃ Pb)
    (Ps : Pl ∘ Pl ~ id) : transport (RP2.elim_type Pb Pl Ps) loop = Pl :=
  !two_quotient.elim_type_incl1

end

attribute RP2.base [constructor]
attribute RP2.rec RP2.elim [unfold 5] [recursor 5]
attribute RP2.elim_type [unfold 4]
attribute RP2.rec_on RP2.elim_on [unfold 2]
attribute RP2.elim_type_on [unfold 1]

section

  protected definition code [unfold 1] : RP2 → Type₀ :=
  begin
    fapply RP2.elim_type,
    { exact bool},
    { exact equiv_bnot},
    { intro b, esimp, induction b: reflexivity}
  end

  theorem is_set_code (x : RP2) : is_set (RP2.code x) :=
  begin
    induction x,
    { change is_set bool, exact _},
    { apply is_prop.elimo},
    { apply is_set.elimo}
  end

  local attribute is_set_code [instance]

  definition transport_code_loop (a : bool) : transport RP2.code loop a = bnot a :=
  ap10 !elim_type_incl1 a

  protected definition encode [unfold 2] (x : RP2) (p : trunc 0 (base = x)) : RP2.code x :=
  begin
    induction p with p, apply transport _ p, exact ff
  end

  attribute bnot [unfold 1]
  protected definition decode (x : RP2) (c : RP2.code x) : trunc 0 (base = x) :=
  begin
    induction x with u u u' r,
    { apply tr, induction c, reflexivity, exact loop},
    { esimp,
      apply arrow_pathover_left, intro b,
      apply trunc_pathover,
      apply eq_pathover_constant_left_id_right,
      xrewrite [↓loop, transport_code_loop], apply square_of_eq,
      induction b,
      { reflexivity},
      { esimp, exact surf}},
    { apply is_set.elimo},
  end

attribute simple_two_quotient.incl0 [constructor]
export [unfold] simple_two_quotient
  protected definition encode_decode (x : RP2) (c : RP2.code x)
    : RP2.encode x (RP2.decode x c) = c :=
  begin
    induction x with u u u' r,
    { induction c, reflexivity, esimp [RP2.decode], apply transport_code_loop},
    { apply pathover_of_tr_eq, apply eq_of_homotopy, intro a, apply @is_set.elim},
    { apply is_set.elimo},
  end

end
end RP2
