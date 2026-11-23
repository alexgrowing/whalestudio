import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EvaluationPowerSeriesShift
import Mathlib
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLtOneOfNotIsUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AwayOfInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyLocalPeriodRingsData
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.BKReal GlobalTheory.Prism Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.DiscEval GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evaluation_power_series_shift : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (L : PowerSeries ↥K.1), OnDisc l (oK K) L →
    ∀ (x : AK K), thetaK K x = 0 → ∀ y : GlobalTheory.AcrisK.BK K, Ev L x y →
    ∃ (L' : PowerSeries ↥K.1) (u : GlobalTheory.AcrisK.BK K), OnDisc l (oK K) L' ∧
      (∀ k, PowerSeries.coeff k L' = PowerSeries.coeff (k + 1) L) ∧ Ev L' x u ∧
      y = inK K (PowerSeries.coeff 0 L) + toB K (ofA K x) * u := by
  first | exact @GlobalTheory.AcrisK.ev_shift | exact GlobalTheory.AcrisK.ev_shift | (intros; apply GlobalTheory.AcrisK.ev_shift <;> assumption)
