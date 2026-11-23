import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCompatiblePowerSeriesValue
import Mathlib
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLtOneOfNotIsUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AwayOfInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyLocalPeriodRingsData
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.BKReal GlobalTheory.Prism Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.DiscEval GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compatible_power_series_value : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (ω : ℕ → AK K) (G : PowerSeries ↥(OL K)) (u : ℕ → OC l),
    (∀ n, frobq K (ω (n + 1)) = ω n) → (∀ n, ‖((thetaK K (ω n) : OC l) : ℂ_[l])‖ < 1) →
    (∀ n, HasSum (fun i => ((intToOC K (PowerSeries.coeff i G) * thetaK K (ω n) ^ i : OC l) : ℂ_[l])) (u n : ℂ_[l])) →
    ∃ y : ℕ → AK K, (∀ n, frobq K (y (n + 1)) = y n) ∧ (∀ n, thetaK K (y n) = u n) ∧
      ∀ M : ℕ, ω 0 ^ M ∣ y 0 - ∑ j ∈ Finset.range M, inO K (PowerSeries.coeff j G) * ω 0 ^ j := by
  first | exact @GlobalTheory.FrobChainSeries.main | exact GlobalTheory.FrobChainSeries.main | (intros; apply GlobalTheory.FrobChainSeries.main <;> assumption)
