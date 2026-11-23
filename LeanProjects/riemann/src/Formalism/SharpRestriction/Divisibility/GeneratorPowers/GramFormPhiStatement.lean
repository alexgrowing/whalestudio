import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCSt

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open NumberField Formalism.MainNotions.ModuliIntegralCharts

def GramFormPhiStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (cj : E → E),
    (∀ (φ : E →+* ℂ) (z : E), φ (cj z) = star (φ z)) → (∃ z : E, cj z ≠ z) →
    ∀ (w₀ : 𝓞 E), (w₀ : E) + cj w₀ = 1 →
    ∀ (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]
      (β : SymB cj Y),
      (∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℤ Y),
        (Matrix.of fun i j => (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b i) (b j)).PosDef) →
      ∃ b : Module.Basis (Fin (Module.finrank ℤ Y)) ℤ Y,
        (∀ j, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b j) (b j) / 2 ≤
          (|(NumberField.discr E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ E)) /
              (2 * Module.finrank ℚ E) * (Module.finrank ℤ Y : ℝ) ^ 3 * phiC cj β) ∧
        ∀ j (z : Y), |(β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b j) z| ≤
          2 * Real.sqrt (Module.finrank ℤ Y) * ((β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) z z / 2)

end Formalism.MainNotions.ModuliIntegralCharts.H1
