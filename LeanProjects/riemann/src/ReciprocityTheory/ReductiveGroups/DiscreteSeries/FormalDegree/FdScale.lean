import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.TraceMulSelfEqSumEigenvaluesSq

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem finrank_pcoord (ε : Fin n → Bool) :
    Module.finrank ℝ (PCoord ε → ℂ) = 2 * (pOf ε * qOf ε) := by
  rw [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ,
    card_PCoord, smul_eq_mul, mul_comm]

theorem lintegral_pcoord_smul {ε : Fin n → Bool} (f : (PCoord ε → ℂ) → ENNReal) {s : ℝ} (hs : 0 < s) :
    ∫⁻ z, f z = ENNReal.ofReal (s ^ (2 * (pOf ε * qOf ε))) * ∫⁻ y, f ((s : ℂ) • y) := by
  have hsm : (fun y : PCoord ε → ℂ => f ((s : ℂ) • y)) = fun y => f (s • y) := by
    funext y
    rw [Complex.coe_smul]
  have key : ∫⁻ y, f (s • y) =
      ENNReal.ofReal |(s ^ Module.finrank ℝ (PCoord ε → ℂ))⁻¹| * ∫⁻ z, f z := by
    have h1 := lintegral_map_equiv f (MeasurableEquiv.smul₀ (α := PCoord ε → ℂ) s hs.ne')
      (μ := volume)
    have h2 : (⇑(MeasurableEquiv.smul₀ (α := PCoord ε → ℂ) s hs.ne')) = (s • ·) := rfl
    rw [h2, Measure.map_addHaar_smul volume hs.ne', lintegral_smul_measure, smul_eq_mul] at h1
    exact h1.symm
  rw [hsm, key, finrank_pcoord, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity), abs_of_pos (by positivity), mul_inv_cancel₀ (by positivity),
    ENNReal.ofReal_one, one_mul]

end ReciprocityTheory.ChartRestriction.DS
