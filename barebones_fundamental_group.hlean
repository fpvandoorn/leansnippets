import hit.trunc
open is_trunc trunc

structure group [class] (G : Type) : Type :=
  (H : is_set G)
  (m : G → G → G)
  (i : G → G)
  (o : G)
  (mul_assoc : Πg₁ g₂ g₃, m (m g₁ g₂) g₃ = m g₁ (m g₂ g₃))
  (mul_one : Πg, m g o = g)
  (one_mul : Πg, m o g = g)
  (mul_left_inv : Πg, m (i g) g = o)
open group

variables {A : Type} {x y z t : A}

definition trunc_eq (x y : A) : Type := trunc 0 (x = y)
infix  ` == `:50  := trunc_eq

definition is_set_trunc_eq [instance] (x y : A) : is_set (x == y) := !is_trunc_trunc

definition is_set_trunc_eq_eq [instance] (p q : x == y) : is_set (p = q) := !is_trunc_eq

definition idp [refl] [constructor] {a : A} : a == a := tr (eq.refl a)

definition concat [trans] [unfold 6] (p : x == y) (q : y == z) : x == z :=
by induction q with q; induction q; exact p

definition inverse [symm] [unfold 4] (p : x == y) : y == x :=
by induction p with p; induction p; reflexivity

infix   ⬝  := concat
postfix ⁻¹ := inverse

definition con_idp [unfold_full] (p : x == y) : p ⬝ idp = p :=
by reflexivity

definition idp_con [unfold 4] (p : x == y) : idp ⬝ p = p :=
by revert p; refine @trunc.rec _ _ _ _ _; intro; apply is_set_trunc_eq_eq; intro p; induction p; reflexivity

definition con.assoc [unfold 8] (p : x == y) (q : y == z) (r : z == t) :
  (p ⬝ q) ⬝ r = p ⬝ (q ⬝ r) :=
by induction r with r; induction r; reflexivity

definition con.left_inv [unfold 4] (p : x == y) : p⁻¹ ⬝ p = idp :=
by induction p with p; induction p; reflexivity

definition fundamental_group : group (x == x) :=
group.mk _ concat inverse idp con.assoc con_idp idp_con con.left_inv
