import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TsumSetIntegralProdEqZeroOfInner
import Mathlib
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tsum_setIntegral_prod_eq_zero_of_inner' : ∀ {G X : Type} [MeasurableSpace G], Countable X → ∀ (ν : Measure G), SFinite ν → ∀ (𝓖 : Set G) (H : X → G × G → ℂ), (∀ x, AEStronglyMeasurable (H x) (ν.prod ν)) → ∫⁻ g₁ in 𝓖, ∫⁻ g₂ in 𝓖, ∑' x, ‖H x (g₁, g₂)‖ₑ ∂ν ∂ν ≠ ⊤ → (∀ g₂, ∑' x, ∫⁻ g₁ in 𝓖, ‖H x (g₁, g₂)‖ₑ ∂ν ≠ ⊤ → ∑' x, ∫ g₁ in 𝓖, H x (g₁, g₂) ∂ν = 0) → ∑' x, ∫ p in 𝓖 ×ˢ 𝓖, H x p ∂(ν.prod ν) = 0 := by
  first | exact @GlobalTheory.tsum_setIntegral_prod_eq_zero_of_inner | exact GlobalTheory.tsum_setIntegral_prod_eq_zero_of_inner | (intros; apply GlobalTheory.tsum_setIntegral_prod_eq_zero_of_inner <;> assumption)
