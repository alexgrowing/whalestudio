import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FlatDegree.Statements
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PFlatDegreeBoundX
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlatTheorem

open NumberField

theorem DifferentNorms.rootDiscr_eq_pow (K E : Type) [Field K] [NumberField K] [Field E]
    [NumberField E] [Algebra K E] :
    rootDiscr K = (((discr K).natAbs : ℝ) ^ Module.finrank K E) ^
      ((Module.finrank ℚ E : ℝ)⁻¹) := by
  have hnE : Module.finrank ℚ E = Module.finrank ℚ K * Module.finrank K E :=
    (Module.finrank_mul_finrank ℚ K E).symm
  have hmpos : 0 < Module.finrank K E := Module.finrank_pos
  have h0 : (0 : ℝ) ≤ ((discr K).natAbs : ℝ) := Nat.cast_nonneg _
  have habsK : ((|discr K| : ℤ) : ℝ) = ((discr K).natAbs : ℝ) := (Nat.cast_natAbs _).symm
  rw [rootDiscr_def, habsK, hnE, ← Real.rpow_natCast, ← Real.rpow_mul h0]
  congr 1
  push_cast
  field_simp

theorem DifferentNorms.proof : DifferentNorms.Statement := by
  intro K E _ _ _ _ _
  have key := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) E (𝓞 E)
  have hK0 : (discr K).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (discr_ne_zero K)
  have hpos : (0 : ℝ) < ((discr K).natAbs : ℝ) ^ Module.finrank K E := by positivity
  have hrdK := DifferentNorms.rootDiscr_eq_pow K E
  refine ⟨?_, ?_, FlatDegreeBound.one_le_rootDiscr K, FlatDegreeBound.rootDiscr_le_rootDiscr K E⟩
  · have hN : (Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 E)) : ℝ) =
        ((discr E).natAbs : ℝ) / ((discr K).natAbs : ℝ) ^ Module.finrank K E := by
      rw [eq_div_iff hpos.ne', key]
      push_cast
      ring
    have habsE : ((|discr E| : ℤ) : ℝ) = ((discr E).natAbs : ℝ) := (Nat.cast_natAbs _).symm
    rw [hN, Real.div_rpow (Nat.cast_nonneg _) hpos.le, ← hrdK, rootDiscr_def E, habsE]
  · rw [Ideal.absNorm_algebraMap, absNorm_differentIdeal K (𝓞 K),
      ← IsFractionRing.finrank_eq (𝓞 K) K (𝓞 E) E, hrdK]
    push_cast
    rfl

end GroundTheory.Heights₂.Heights.FlatTheorem
