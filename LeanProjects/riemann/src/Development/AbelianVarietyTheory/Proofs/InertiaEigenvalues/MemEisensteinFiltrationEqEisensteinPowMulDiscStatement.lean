import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemEisensteinFiltrationEqEisensteinPowMulDisc
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ImagePolynomialAction
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_eisensteinFiltration_eq_eisenstein_pow_mul_disc : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (j : ℕ), ∀ φ : S O K e, φ ∈ Fil O K l e j → ∃ q ∈ Rpi O K l e, (φ : K⟦X⟧) = E K l e ^ j * q := by
  first | exact @GlobalTheory.FilDiv.mem_Fil_eq_E_pow_mul | exact GlobalTheory.FilDiv.mem_Fil_eq_E_pow_mul | (intros; apply GlobalTheory.FilDiv.mem_Fil_eq_E_pow_mul <;> assumption)
