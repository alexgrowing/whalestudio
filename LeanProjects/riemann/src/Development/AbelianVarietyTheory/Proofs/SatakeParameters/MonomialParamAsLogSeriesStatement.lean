import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MonomialParamAsLogSeries
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inParam_eq_monomial_low_coeff_zero : ∀ (p : ℕ) [Fact p.Prime] (ι : Type) [Fintype ι] (n : ι →₀ ℕ), ∃ U : MvPowerSeries ι (K0 p), inParam p U = MvPowerSeries.monomial n 1 ∧ (∀ m : ι →₀ ℕ, m.degree < n.degree → MvPowerSeries.coeff m U = 0) := by
  first | exact @GlobalTheory.TwU.monomial_param_as_log_series | exact GlobalTheory.TwU.monomial_param_as_log_series | (intros; apply GlobalTheory.TwU.monomial_param_as_log_series <;> assumption)
