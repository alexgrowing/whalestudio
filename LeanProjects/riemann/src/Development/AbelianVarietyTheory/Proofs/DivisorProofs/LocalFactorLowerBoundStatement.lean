import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFactorLowerBound
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsMulMulConjTransposeEqOne
open NumberField IsDedekindDomain GlobalTheory.SUVol
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_factor_lower_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))), 1 ≤ r →
    (v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))).IsPrime →
    ∏ i ∈ Finset.Icc 2 r, (1 - ((Ideal.absNorm v.asIdeal : ℝ) ^ i)⁻¹) ≤ locFactor E r v := by
  first | exact @GlobalTheory.SUVol.prod_le_locFactor_of_isPrime | exact GlobalTheory.SUVol.prod_le_locFactor_of_isPrime | (intros; apply GlobalTheory.SUVol.prod_le_locFactor_of_isPrime <;> assumption)
