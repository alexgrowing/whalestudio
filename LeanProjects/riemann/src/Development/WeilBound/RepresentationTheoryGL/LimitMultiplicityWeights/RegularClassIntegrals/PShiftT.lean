import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.ClosedGraph

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel.PShiftT

def rho (S : ℂ → ℝ) (z : ℂ) : ℂ :=
  if 1 < ‖z‖ then ((Real.sqrt (S z) : ℝ) : ℂ)
  else if ‖z‖ < 1 then (((Real.sqrt (S (star z)⁻¹) : ℝ) : ℂ))⁻¹ else 1

lemma key (S : ℂ → ℝ) (hS : ∀ z, 0 < S z) (z w : ℂ) (h : star z * w = 1) :
    star (rho S z) * rho S w = 1 := by
  have hz : z ≠ 0 := by rintro rfl; simp at h
  have hw : w = (star z)⁻¹ := eq_inv_of_mul_eq_one_right h
  subst hw
  have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hn : ‖(star z)⁻¹‖ = ‖z‖⁻¹ := by rw [norm_inv, norm_star]
  have hcc : (star (star z)⁻¹)⁻¹ = z := by rw [star_inv₀, star_star, inv_inv]
  have e : ‖z‖ * ‖z‖⁻¹ = 1 := mul_inv_cancel₀ hpos.ne'
  have hipos : 0 < ‖z‖⁻¹ := inv_pos.mpr hpos
  rcases lt_trichotomy 1 ‖z‖ with h1 | h1 | h1
  · have h2 : ‖z‖⁻¹ < 1 := by nlinarith
    have hs : (((Real.sqrt (S z)) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hS z)).ne'
    simp only [rho, hn, hcc]
    rw [if_pos h1, if_neg (by linarith), if_pos h2, Complex.star_def, Complex.conj_ofReal]
    exact mul_inv_cancel₀ hs
  · have h2 : ‖z‖⁻¹ = 1 := by rw [← h1, inv_one]
    simp only [rho, hn, hcc]
    rw [if_neg (by linarith), if_neg (by linarith), if_neg (by linarith), if_neg (by linarith)]
    simp
  · have h2 : 1 < ‖z‖⁻¹ := by nlinarith
    have hs : (((Real.sqrt (S (star z)⁻¹)) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hS _)).ne'
    simp only [rho, hn, hcc]
    rw [if_neg (by linarith), if_pos h1, if_pos h2, star_inv₀, Complex.star_def, Complex.conj_ofReal]
    exact inv_mul_cancel₀ hs

end MainStatements.WeightKernel.PShiftT

namespace MainStatements.WeightKernel

open MainStatements.WeightKernel.PShiftT in
theorem shiftT : ShiftT := by
  intro n J l hl hJ σ hσ
  classical
  let S : ℂ → ℝ := fun z => if h : ∃ i, l i = z then σ (Classical.choose h) else 1
  have hSpos : ∀ z, 0 < S z := by
    intro z
    simp only [S]
    split_ifs
    · exact hσ _
    · exact zero_lt_one
  have hSl : ∀ i, S (l i) = σ i := by
    intro i
    have h : ∃ j, l j = l i := ⟨i, rfl⟩
    simp only [S, dif_pos h]
    rw [hl (Classical.choose_spec h)]
  refine ⟨fun i => rho S (l i), ?_, ?_⟩
  · ext i j
    have hij := congrFun (congrFun hJ i) j
    simp only [diagonal_conjTranspose, mul_diagonal, diagonal_mul, Pi.star_apply] at hij ⊢
    by_cases h0 : J i j = 0
    · simp [h0]
    have e1 : star (l i) * l j = 1 := by
      have : (star (l i) * l j) * J i j = 1 * J i j := by rw [one_mul]; calc _ = star (l i) * J i j * l j := by ring
          _ = J i j := hij
      exact mul_right_cancel₀ h0 this
    have e2 : star (rho S (l i)) * rho S (l j) = 1 := key S hSpos _ _ e1
    calc _ = (star (rho S (l i)) * rho S (l j)) * J i j := by ring
      _ = J i j := by rw [e2, one_mul]
  · intro i hi
    show ‖rho S (l i)‖ ^ 2 = σ i
    rw [rho, if_pos hi, hSl, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (hσ i).le]

end MainStatements.WeightKernel

end
