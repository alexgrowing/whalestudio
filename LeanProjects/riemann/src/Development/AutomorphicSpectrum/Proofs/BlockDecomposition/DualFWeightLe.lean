import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.UnipotentTateFunctionalEquation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.FunctionalEquationGL2GL1Complex
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GauIntegrable
open MeasureTheory

namespace GlobalTheory.CompanionTheory.Parseval

lemma geom_real (p q r s ζ N D : ℝ) (hD : D = p * s - q * r) (hD0 : D ≠ 0) (hN : 0 ≤ N)
    (h0 : |(s * ζ - r) / D| ≤ N) (h1 : |(p - q * ζ) / D| ≤ N) :
    ((1 + N) ^ 2)⁻¹ ≤ 4 * ((1 + |ζ - (p * q + r * s) / (q ^ 2 + s ^ 2)| /
      (|D| / Real.sqrt (q ^ 2 + s ^ 2))) ^ 2)⁻¹ := by
  have hm : 0 < q ^ 2 + s ^ 2 := by
    rcases eq_or_ne q 0 with hq | hq
    · rcases eq_or_ne s 0 with hs | hs
      · exact absurd (by rw [hD, hq, hs]; ring) hD0
      · positivity
    · positivity
  obtain ⟨m, hmdef⟩ : ∃ m, m = q ^ 2 + s ^ 2 := ⟨_, rfl⟩
  obtain ⟨l, hldef⟩ : ∃ l, l = (p * q + r * s) / (q ^ 2 + s ^ 2) := ⟨_, rfl⟩
  rw [← hldef, ← hmdef]
  rw [← hmdef] at hm
  obtain ⟨t, htdef⟩ : ∃ t, t = |ζ - l| / (|D| / Real.sqrt m) := ⟨_, rfl⟩
  rw [← htdef]
  have ht0 : 0 ≤ t := by rw [htdef]; positivity
  have hD2 : 0 < D ^ 2 := by positivity
  have ht2 : t ^ 2 = (ζ - l) ^ 2 * m / D ^ 2 := by
    rw [htdef, div_pow, div_pow, sq_abs, sq_abs, Real.sq_sqrt hm.le]
    field_simp
  have hid : (s * ζ - r) ^ 2 + (p - q * ζ) ^ 2 = m * (ζ - l) ^ 2 + D ^ 2 / m := by
    rw [hldef, ← hmdef]
    have hm' : m ≠ 0 := hm.ne'
    field_simp
    rw [hD, hmdef]
    ring
  have hx : ((s * ζ - r) / D) ^ 2 ≤ N ^ 2 := sq_le_sq.2 (by rwa [abs_of_nonneg hN])
  have hy : ((p - q * ζ) / D) ^ 2 ≤ N ^ 2 := sq_le_sq.2 (by rwa [abs_of_nonneg hN])
  have hsum : ((s * ζ - r) / D) ^ 2 + ((p - q * ζ) / D) ^ 2 = t ^ 2 + 1 / m := by
    rw [div_pow, div_pow, ← add_div, hid, ht2]
    field_simp
  have hinv : 0 < 1 / m := by positivity
  have ht4 : t ^ 2 ≤ 2 * N ^ 2 := by linarith
  have ht : t ≤ 2 * N := by
    by_contra hc
    push_neg at hc
    nlinarith
  have hle : (1 + t) ^ 2 ≤ 4 * (1 + N) ^ 2 := by nlinarith
  rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

theorem dualF_weight_le : ∀ (h : Ad3.LR.M22) (ζ : ℝ), (Matrix.of h).det ≠ 0 →
    ((1 + ‖GlobalTheory.CompanionTheory.Parseval.dualF h ζ‖) ^ 2)⁻¹ ≤ 4 * GlobalTheory.CompanionTheory.Parseval.wt
      (|(Matrix.of h).det| / Real.sqrt (h 0 1 ^ 2 + h 1 1 ^ 2))
      ((h 0 0 * h 0 1 + h 1 0 * h 1 1) / (h 0 1 ^ 2 + h 1 1 ^ 2)) ζ := by
  intro h ζ hD
  have hdet : (Matrix.of h).det = h 0 0 * h 1 1 - h 0 1 * h 1 0 := by
    rw [Matrix.det_fin_two]
    rfl
  have h0 := norm_le_pi_norm (dualF h ζ) 0
  have h1 := norm_le_pi_norm (dualF h ζ) 1
  rw [Real.norm_eq_abs] at h0 h1
  exact geom_real (h 0 0) (h 0 1) (h 1 0) (h 1 1) ζ _ _ hdet hD (norm_nonneg _) h0 h1

end GlobalTheory.CompanionTheory.Parseval
