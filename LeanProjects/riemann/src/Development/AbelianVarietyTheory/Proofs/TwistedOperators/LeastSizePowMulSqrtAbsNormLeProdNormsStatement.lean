import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeastSizePowMulSqrtAbsNormLeProdNorms
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
open MeasureTheory NumberField Matrix Formalism.MainNotions.S GlobalTheory.Count Formalism.REAL Formalism.HN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leastSize_pow_mul_sqrt_absNorm_le_prod_norms : ∀ (I : AutInst) (x : I.GA) (𝔪 : Ideal (𝓞 I.E)), 𝔪 ≠ ⊥ → ∀ w ∈ 𝔪 • lamX I x, w ≠ 0 → least I x ^ I.f * Real.sqrt (Ideal.absNorm 𝔪) ≤ ∏ v, Real.sqrt (∑ i, ‖(uMat (x.1 v)⁻¹ *ᵥ ((I.P v)⁻¹ *ᵥ fun j => I.φ v (w j))) i‖ ^ 2) := by
  first | exact @GlobalTheory.LineBound.least_pow_mul_sqrt_absNorm_le_prod | exact GlobalTheory.LineBound.least_pow_mul_sqrt_absNorm_le_prod | (intros; apply GlobalTheory.LineBound.least_pow_mul_sqrt_absNorm_le_prod <;> assumption)
