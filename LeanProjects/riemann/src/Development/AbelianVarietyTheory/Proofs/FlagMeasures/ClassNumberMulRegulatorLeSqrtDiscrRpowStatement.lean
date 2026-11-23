import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClassNumberMulRegulatorLeSqrtDiscrRpow
import Formalism.HermitianLattices.StatementMass
open MeasureTheory NumberField Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classNumber_mul_regulator_le_sqrt_discr_rpow' : ∀ (K : Type) [Field K] [NumberField K], IsTotallyComplex K → ∀ s : ℝ, 1 < s → (classNumber K : ℝ) * Units.regulator K ≤ Real.sqrt |(discr K : ℝ)| ^ s * (s / (s - 1)) ^ Module.finrank ℚ K := by
  first | exact @GlobalTheory.classNumber_mul_regulator_le_sqrt_discr_rpow | exact GlobalTheory.classNumber_mul_regulator_le_sqrt_discr_rpow | (intros; apply GlobalTheory.classNumber_mul_regulator_le_sqrt_discr_rpow <;> assumption)
