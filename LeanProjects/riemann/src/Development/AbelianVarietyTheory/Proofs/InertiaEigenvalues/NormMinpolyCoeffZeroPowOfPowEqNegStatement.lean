import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormMinpolyCoeffZeroPowOfPowEqNeg
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_minpoly_coeff_zero_pow_of_pow_eq_neg_prime : ∀ (l : ℕ) [Fact l.Prime] (F : IntermediateField ℚ_[l] (Om l)) (N : ℕ) (x : Om l), 0 < N → x ^ N = -(l : Om l) → ‖(((minpoly F x).coeff 0 : F) : Om l)‖ ^ N = ((l : ℝ)⁻¹) ^ (minpoly F x).natDegree := by
  first | exact @GlobalTheory.norm_minpoly_coeff_zero_pow_of_pow_eq_neg | exact GlobalTheory.norm_minpoly_coeff_zero_pow_of_pow_eq_neg | (intros; apply GlobalTheory.norm_minpoly_coeff_zero_pow_of_pow_eq_neg <;> assumption)
