import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumUniversalDeterminantDatumCoeffEqPrimitive
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardSubspacesSupEqTop
open Matrix GlobalTheory.ExportSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_universalDeterminantDatumCoeff_eq_primitive : ∀ (k C : Type) [Field k] [Finite k] [AddCommGroup C] [Fintype C] (r n : ℕ), r ≤ n → ∀ (β : DetBases k r n) (κ : kˣ →* Multiplicative C) (y : Matrix (Fin r) (Fin n) k), ∑ c, univCoef β κ c y = prim y := by
  first | exact @GlobalTheory.ExportSeries.sum_univCoef_eq_prim | exact GlobalTheory.ExportSeries.sum_univCoef_eq_prim | (intros; apply GlobalTheory.ExportSeries.sum_univCoef_eq_prim <;> assumption)
