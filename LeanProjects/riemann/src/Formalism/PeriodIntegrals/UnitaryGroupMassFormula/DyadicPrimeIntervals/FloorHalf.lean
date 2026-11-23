import Mathlib
import Formalism.PeriodIntegrals.PrimesDyadicRS
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicPrimeIntervals.ThetaDiff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.PsiLowerBoundHolds

namespace PI.PrimesDyadicRS.W

theorem floor_half (y : ℝ) : ⌊y⌋₊ = ⌊2 * y⌋₊ / 2 := by
  have e : (2 * y) / ((2 : ℕ) : ℝ) = y := by push_cast; ring
  calc ⌊y⌋₊ = ⌊(2 * y) / ((2 : ℕ) : ℝ)⌋₊ := by rw [e]
    _ = ⌊2 * y⌋₊ / 2 := Nat.floor_div_natCast _ _

theorem small_of (hS : SmallNat) : ∀ y : ℝ, 41 / 2 ≤ y → y < 65536 → At y := by
  intro y h1 h2
  have hy0 : 0 ≤ 2 * y := by linarith
  have h41 : 41 ≤ ⌊2 * y⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hlt : ⌊2 * y⌋₊ < 131072 := (Nat.floor_lt hy0).2 (by push_cast; linarith)
  have key := hS _ h41 hlt
  have hhy : (⌊2 * y⌋₊ : ℝ) ≤ 2 * y := Nat.floor_le hy0
  have hyh : 2 * y < ⌊2 * y⌋₊ + 1 := Nat.lt_floor_add_one _
  have h41r : (41 : ℝ) ≤ ⌊2 * y⌋₊ := by exact_mod_cast h41
  have hh2 : (0 : ℝ) < (⌊2 * y⌋₊ : ℝ) / 2 := by linarith
  have hlog0 : 0 < Real.log ((⌊2 * y⌋₊ : ℝ) / 2) := Real.log_pos (by linarith)
  have hlog : Real.log ((⌊2 * y⌋₊ : ℝ) / 2) ≤ Real.log y := Real.log_le_log hh2 (by linarith)
  have hlogy : 0 < Real.log y := lt_of_lt_of_le hlog0 hlog
  unfold At
  rw [floor_half y]
  set D := (Nat.primeCounting ⌊2 * y⌋₊ : ℝ) - (Nat.primeCounting (⌊2 * y⌋₊ / 2) : ℝ) with hDdef
  have hD : 0 < D := by
    by_contra hc
    push_neg at hc
    nlinarith [mul_le_mul_of_nonneg_right hc hlog0.le]
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hlog hD.le]

theorem large_of (hT : ThetaDiff) (hP : PsiTheta) (hR : RealIneq) :
    ∀ y : ℝ, 65536 ≤ y → At y := by
  intro y hy
  have h1 := PI.PC.psiLowerBound_holds (2 * y) (by linarith)
  have h2 := PI.PC.psiUpperBound_holds y (by linarith)
  have h3 := hP (2 * y) (by linarith)
  have hs : (1 : ℝ) ≤ Real.sqrt (2 * y) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith)
  have h4 := PI.PC.psiUpperBound_holds (Real.sqrt (2 * y)) hs
  have h5 := Chebyshev.theta_le_psi y
  have h6 := hT y (by linarith)
  have h7 := hR y hy
  have hL : 0 < Real.log (2 * y) := Real.log_pos (by linarith)
  unfold At
  have h8 : 3 * y / (5 * Real.log y) * Real.log (2 * y) <
      ((Nat.primeCounting ⌊2 * y⌋₊ : ℝ) - (Nat.primeCounting ⌊y⌋₊ : ℝ)) * Real.log (2 * y) := by
    linarith
  exact lt_of_mul_lt_mul_right h8 hL.le

theorem claim_of (hS : SmallNat) (hT : ThetaDiff) (hP : PsiTheta) (hR : RealIneq) :
    PI.PrimesDyadicRS.Claim := by
  intro y hy
  rcases lt_or_ge y 65536 with h | h
  · exact small_of hS y hy h
  · exact large_of hT hP hR y h

end PI.PrimesDyadicRS.W
