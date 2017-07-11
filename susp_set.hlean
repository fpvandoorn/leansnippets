
/---------------------------------------------------------------------------------------------------
Is the suspension of sets without decidable equality a 1-type?
---------------------------------------------------------------------------------------------------/

import homotopy.susp types.int ..Spectral.algebra.group_constructions

open susp eq bool is_trunc quotient unit pointed equiv prod int pi algebra group trunc lift

namespace susp
  /- move to library -/

  attribute bnot bnot_bnot [unfold 1]

  definition susp.rec_prop [unfold 6] {A : Type} {P : susp A → Type}
    [Πx, is_prop (P x)] (pn : P north) (ps : P south) (x : susp A) : P x :=
  susp.rec pn ps (λa, !is_prop.elimo) x

  definition susp_flip [unfold 2] {A : Type} (x : susp A) : susp A :=
  begin
    induction x with a,
    { exact south},
    { exact north},
    { exact (merid a)⁻¹ },
  end

  definition susp_flip_susp_flip [unfold 2] {A : Type} (x : susp A) : susp_flip (susp_flip x) = x :=
  begin
    induction x with b,
    { reflexivity },
    { reflexivity },
    { apply eq_pathover_id_right, apply hdeg_square,
      rewrite [ap_compose' susp_flip susp_flip, ↑susp_flip, elim_merid, ▸*, ap_inv, elim_merid, ▸*],
      apply inv_inv },
  end

  definition susp_flip_equiv [constructor] (A : Type) : susp A ≃ susp A :=
  equiv.MK susp_flip susp_flip susp_flip_susp_flip susp_flip_susp_flip

  /- end move to library -/

  /- First something easier: the suspension of a mere proposition is a set -/
  section
  universe variable u
  parameter (P : Prop.{u})

  definition X : Type* := psusp P

  definition code [unfold 2] : X → Prop.{u} :=
  begin
    intro x, induction x,
    { exact trunctype.mk (lift unit) _},
    { exact P},
    { apply tua, esimp, apply equiv_of_is_prop,
      { intro u, exact a },
      { intro p, exact up ⋆ }}
  end

  definition encode [unfold 3] (x : X) (p : north = x) : code x :=
  transport code p (up ⋆)

  definition decode [unfold 2 3] (x : X) (c : code x) : north = x :=
  begin
    induction x with b,
    { reflexivity },
    { esimp at c, exact merid c },
    { apply arrow_pathover_left, intro c,
      apply eq_pathover_constant_left_id_right, esimp at *, apply square_of_eq,
      refine !idp_con ⬝ _ ⬝ !idp_con⁻¹, apply ap merid !is_prop.elim }
  end

  definition decode_encode (x : X) (p : north = x) : decode x (encode x p) = p :=
  begin
    induction p, reflexivity
  end

  definition encode_decode (x : X) (c : code x) : encode x (decode x c) = c :=
  !is_prop.elim

  definition X_eq [constructor] (x : X) : (north = x) ≃ code x :=
  equiv.MK (encode x) (decode x) (encode_decode x) (decode_encode x)

  definition is_set_X : is_set X :=
  begin
    apply is_trunc_succ_intro,
    intro x y,
    assert H : Π(y : X), is_prop (north = y),
    { intro y, exact is_trunc_equiv_closed_rev _ (X_eq y) },
    induction x using susp.rec_prop,
    { apply H },
    { apply @(is_trunc_equiv_closed_rev _ (eq_equiv_fn_eq_of_equiv !susp_flip_equiv south y)),
      apply H }
  end

  definition is_set_susp [instance] (A : Type) [is_prop A] : is_set (susp A) :=
  susp.is_set_X (trunctype.mk A _)

  definition is_set_psusp [instance] (A : Type) [is_prop A] : is_set (psusp A) :=
  is_set_susp A

  definition Xs [constructor] : Set := trunctype.mk X is_set_X

  definition Y := psusp X
  definition tℤ : Set := trunctype.mk ℤ _

  definition loop : north = north :> Y :=
  merid south ⬝ (merid north)⁻¹

  definition Ycode [unfold 2] : Y → Set.{0} :=
  begin
    intro y, induction y with x,
    { exact tℤ }, --if P then unit else ℤ, except implement it using quotients with paths from P
    { exact tℤ }, --
    { apply tua, induction x with b,
      { reflexivity },
      { apply equiv_succ },
      { apply equiv_eq, intro x, exact sorry }}
  end

  definition Yencode [unfold 3] (y : Y) (p : north = y) : Ycode y :=
  transport Ycode p (0 : ℤ)

  definition Ydecode [unfold 2 3] (y : Y) (c : Ycode y) : north = y :=
  begin
    induction y,
    { exact power loop c },
    { exact power loop c ⬝ merid north },
    { apply arrow_pathover_left, intro c,
      apply eq_pathover_constant_left_id_right, esimp at *, exact sorry }
  end

  definition Ydecode_encode (y : Y) (p : north = y) : Ydecode y (Yencode y p) = p :=
  begin
    induction p, reflexivity
  end

  definition Yencode_decode (y : Y) (c : Ycode y) : Yencode y (Ydecode y c) = c :=
  begin
    induction y,
    { exact sorry },
    { exact sorry },
    { apply is_prop.elimo }
  end


  end
end susp

/- some group theory -/
namespace group

  definition mul_left_equiv {G : Group} (g : G) : G ≃ G :=
  begin
    fapply equiv.MK,
    { intro h, exact g * h },
    { intro h, exact g⁻¹ * h },
    { intro h, apply mul_inv_cancel_left },
    { intro h, apply inv_mul_cancel_left }
  end

end group
open group

open susp
namespace hide_susp

  section
  universe variable u
  parameter (A : pSet.{u})

  definition X : Type* := psusp A

  definition susp_loop {A : Type*} (a : A) : north = north :> susp A :=
  merid a ⬝ (merid pt)⁻¹

  definition code [unfold 2] : X → Set.{u} :=
  begin
    intro x, induction x with a,
    { exact Set_of_Group (free_group A) },
    { exact Set_of_Group (free_group A) },
    { apply tua, apply mul_left_equiv, apply free_group_inclusion, exact a }
  end

  definition encode [unfold 3] (x : X) (p : north = x) : code x :=
  transport code p (@one (free_group A) _)

exit
  definition decode_north [unfold 2 3] (c : free_group A) : north = north :> X :=
  begin
    induction c with l l l' H, -- this is not allowed
    { induction l with v l p,
      { reflexivity },
      { induction v with a a,
        { exact p ⬝ susp_loop a },
        { exact p ⬝ (susp_loop a)⁻¹ }}},
    { esimp at *, exact sorry }
  end

  definition decode [unfold 2 3] (x : X) (c : code x) : north = x :=
  begin
    induction x with b,
    { },
    { esimp at c, exact merid c },
    { apply arrow_pathover_left, intro c,
      apply eq_pathover_constant_left_id_right, esimp at *, apply square_of_eq,
      refine !idp_con ⬝ _ ⬝ !idp_con⁻¹, apply ap merid !is_prop.elim }
  end

  definition decode_encode (x : X) (p : north = x) : decode x (encode x p) = p :=
  begin
    induction p, reflexivity
  end

  definition encode_decode (x : X) (c : code x) : encode x (decode x c) = c :=
  !is_prop.elim

  definition X_eq [constructor] (x : X) : (north = x) ≃ code x :=
  equiv.MK (encode x) (decode x) (encode_decode x) (decode_encode x)

  definition is_set_X [instance] : is_set X :=
  begin
    apply is_trunc_succ_intro,
    intro x y,
    assert H : Π(y : X), is_prop (north = y),
    { intro y, exact is_trunc_equiv_closed_rev _ (X_eq y) },
    induction x using susp.rec_prop,
    { apply H },
    { apply @(is_trunc_equiv_closed_rev _ (eq_equiv_fn_eq_of_equiv !susp_flip_equiv south y)),
      apply H }
  end

  definition Xs [constructor] : Set := trunctype.mk X _

  end

end hide_susp
