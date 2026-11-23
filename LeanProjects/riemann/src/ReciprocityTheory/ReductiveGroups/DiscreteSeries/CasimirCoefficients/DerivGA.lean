import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

section PathL
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma dga_exp (W : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • W)) W 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) W (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  have e : (fun t : ℝ => NormedSpace.exp ((t : ℂ) • W)) = fun u : ℝ => NormedSpace.exp (u • W) := by
    funext t
    rw [Complex.coe_smul]
  rw [e]
  exact h

lemma dga_path (Y z : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (-((t : ℂ) • Y)) * z * NormedSpace.exp ((t : ℂ) • Y))
      (z * Y - Y * z) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => NormedSpace.exp (-((t : ℂ) • Y))) (-Y) 0 := by
    have h := dga_exp (-Y)
    simpa [smul_neg] using h
  have h2 := dga_exp Y
  have e0 : NormedSpace.exp (((0 : ℝ) : ℂ) • Y) = 1 := by simp
  have e1 : NormedSpace.exp (-(((0 : ℝ) : ℂ) • Y)) = 1 := by simp
  have h3 := (h1.mul_const z).mul h2
  simp only [e0, e1, mul_one, one_mul] at h3
  have e2 : -Y * z + z * Y = z * Y - Y * z := by noncomm_ring
  rw [e2] at h3
  exact h3

end PathL

end ReciprocityTheory.ChartRestriction.DS.S7
