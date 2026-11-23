import Formalism.GaussValuationBounds.Statement

namespace Formalism.NOK

theorem expNonzero_proof : ExpNonzero := by
  intro g b hg hgb x hx
  simp only [Finset.mem_union, Finset.mem_Icc] at hx
  omega

theorem eTotal_proof : ETotal := by
  intro r s k g e hr hs hg he
  rw [max_eq_right (by nlinarith [mul_nonneg hg he])]; ring

theorem exponentSumIdentity : ExponentSumIdentity := by
  intro l b b' S E lam hl
  have h1 : l - 1 ≠ 0 := by linarith
  have h2 : l ≠ 0 := by linarith
  field_simp; ring

theorem slopeNum_proof : SlopeNum := by
  refine ⟨fun l hl => ?_, by norm_num⟩
  have h1 : 0 < l - 1 := by linarith
  rw [div_add_div _ _ (by positivity) (by positivity), div_lt_div_iff₀ (by positivity) (by linarith)]
  nlinarith [sq_nonneg (l-13), mul_pos h1 h1, mul_pos (mul_pos h1 h1) h1, sq_nonneg l,
    mul_pos (mul_pos (mul_pos h1 h1) h1) h1]

end Formalism.NOK
