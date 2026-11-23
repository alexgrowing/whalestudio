import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimultaneousUnitsModN
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simultaneous_units_mod_n : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (N : ℕ), 0 < N → ∀ T₁ T₂ : 𝓞 E →+ ℤ, (∀ c, T₁ (H.bar c) = - T₁ c) → (∀ c, T₂ (H.bar c) = - T₂ c) → (∀ c : 𝓞 E, (∀ d : 𝓞 E, (N : ℤ) ∣ T₁ (c * d)) → ∃ b : 𝓞 E, c = N • b) → (∀ c : 𝓞 E, (∀ d : 𝓞 E, (N : ℤ) ∣ T₂ (c * d)) → ∃ b : 𝓞 E, c = N • b) → ∃ μ ν : 𝓞 E, (∃ b : 𝓞 E, μ * ν - 1 = N • b) ∧ (∃ b : 𝓞 E, H.bar μ - μ = N • b) ∧ ∀ c : 𝓞 E, (N : ℤ) ∣ T₁ (μ * c) - T₂ c := by
  first | exact @GlobalTheory.DualUnit.dual_unit | exact GlobalTheory.DualUnit.dual_unit | (intros; apply GlobalTheory.DualUnit.dual_unit <;> assumption)
