

import .chain_complex algebra.homotopy_group

open eq equiv is_equiv sigma sigma.ops fiber pointed

namespace hide
section

  definition ezmap [constructor] {X Y Z : Type} (f : X → Y) (g : Y → Z) (z₀ : Z)
                   (p : Πx, g (f x) = z₀) : X → fiber g z₀ := λx, fiber.mk (f x) (p x)

  definition fibration_sequence {X Y Z : Type} (f : X → Y) (g : Y → Z) (z₀ : Z) : Type :=
  Σ(p : Πx, g (f x) = z₀), is_equiv (ezmap f g z₀ p)

  parameters {X Y Z : Type} (f : X → Y) (g : Y → Z) (z₀ : Z) (v : fibration_sequence f g z₀)
             (y₀ : Y) (q : g y₀ = z₀) (x₀ : X) (r : f x₀ = y₀)

  definition is_equiv_ezmap [instance] : is_equiv (ezmap f g z₀ v.1) := v.2

  definition d1 : z₀ = z₀ → X :=
  λl, (ezmap f g z₀ v.1)⁻¹ (fiber.mk y₀ (q ⬝ l))

  definition derived_sequence : fibration_sequence d1 f y₀ :=
  begin
    fconstructor,
    { intro p, unfold d1,
      refine @(inv_homotopy_of_homotopy' (ezmap f g z₀ v.1))
               _ fiber.point _ _ (fiber.mk y₀ (q ⬝ p)),
      reflexivity},
    { exact sorry}
  end

  definition d2 : y₀ = y₀ → z₀ = z₀ :=
  λp, q⁻¹ ⬝ ap g p ⬝ q
  include r
  definition derived_sequence2 : fibration_sequence d2 d1 x₀ :=
  begin
    fconstructor,
    { intro p, unfold [d1, d2],
      apply inv_eq_of_eq, fapply fiber_eq: esimp,
      { exact r⁻¹},
      { exact sorry}},
    { exact sorry}
  end


end
end hide


section

  definition ezmap [constructor] {X Y Z : Type*} (f : X →* Y) (g : Y →* Z)
                   (p : Πx, g (f x) = pt) : X → pfiber g := λx, fiber.mk (f x) (p x)

  definition fibration_sequence {X Y Z : Type*} (f : X →* Y) (g : Y →* Z) : Type :=
  Σ(p : Πx, g (f x) = pt), is_equiv (ezmap f g p)

  parameters {X Y Z : Type*} (f : X →* Y) (g : Y →* Z) (v : fibration_sequence f g)

  definition is_equiv_ezmap [instance] : is_equiv (ezmap f g v.1) := v.2

  -- set_option pp.coercions true
  definition d1 [constructor] : Ω Z →* X :=
  pmap.mk (λl, (ezmap f g v.1)⁻¹ (fiber.mk pt (respect_pt g ⬝ l)))
    begin
      esimp, apply @inv_eq_of_eq, fapply fiber_eq: esimp,
      { exact !respect_pt⁻¹},
      { exact sorry}
    end

  definition derived_sequence : fibration_sequence d1 f :=
  begin
    fconstructor,
    { intro p, unfold d1,
      refine @(inv_homotopy_of_homotopy' (ezmap f g v.1))
               _ fiber.point _ _ (fiber.mk pt (_ ⬝ p)),
      reflexivity},
    { exact sorry}
  end
exit
  definition d2 : y₀ = y₀ → z₀ = z₀ :=
  λp, q⁻¹ ⬝ ap g p ⬝ q
  include r
  definition derived_sequence2 : fibration_sequence d2 d1 x₀ :=
  begin
    fconstructor,
    { intro p, unfold [d1, d2],
      apply inv_eq_of_eq, fapply fiber_eq: esimp,
      { exact r⁻¹},
      { }},
    { exact sorry}
  end


end
