/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn
-/

import .type_quotient .interval arity

open type_quotient eq interval
exit
namespace two_quotient

  section
  parameters {A : Type}
             (R : A → A → Type)
             (Q : Π⦃a a'⦄, R a a' → R a a' → Type)
  variables {a a' : A} {t b : R a a'}

  definition pre_two_quotient := type_quotient R
  local abbreviation B := pre_two_quotient
  inductive two_quotient_rel : B → B → Type :=
  | Rmk : Π{a a' : A} {t : R a a'} {b : R a a'}, Q b t → Π(x : interval),
           two_quotient_rel (interval.elim_on x (!class_of a) (!class_of a') (!eq_of_rel t))
                            (interval.elim_on x (!class_of a) (!class_of a') (!eq_of_rel b))

  definition two_quotient := type_quotient two_quotient_rel
  local abbreviation C := two_quotient

  definition incl0 (a : A) : C := !class_of (!class_of a)
  definition incl1 (H : R a a') : incl0 a = incl0 a' := ap !class_of (!eq_of_rel H)
  definition incl2 (H : Q t b) : incl1 t = incl1 b :=
  begin
  --refine (!elim_seg⁻¹ ⬝ _ ⬝ !elim_seg), esimp,
  --apply concat, rotate 1, apply idp_con,
  refine (_ ⬝ @ap_con_eq_con_ap _ _  (interval.elim (class_of two_quotient_rel (class_of R a))
       (class_of two_quotient_rel (class_of R a'))
       (incl1 t)) (interval.elim (class_of two_quotient_rel (class_of R a))
       (class_of two_quotient_rel (class_of R a'))
       (incl1 b))   _ _ _ seg ⬝ _),
  { intro x, },
  -- apply apd011 (λx y, ap x y),
--  rewrite [↑incl1,-elim_seg],
  end
--apply concat,    eq_of_homotopy (λx, eq_of_rel two_quotient_rel (two_quotient_rel.Rmk t b x))
  end

end two_quotient

exit

-- below an attempt for a "cubical" two_quotient_rel

namespace two_quotient

  section
  parameters {A : Type}
             (R : A → A → Type)
             (Q : Π⦃a b c d : A⦄, R a b → R c d → R a c → R b c → Type)

  definition pre_two_quotient := type_quotient R
  local abbreviation B := pre_two_quotient
  inductive two_quotient_rel : B → B → Type :=
  | Rs : Π{a b' c d : A} (t : R a b') (b : R c d) (l : R a c) (r : R b' d) (x : interval),
           two_quotient_rel (interval.elim_on x _ _ _) _

  end

end two_quotient
