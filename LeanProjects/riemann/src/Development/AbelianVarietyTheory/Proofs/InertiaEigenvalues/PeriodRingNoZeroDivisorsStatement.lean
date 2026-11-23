import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodRingNoZeroDivisors
import Mathlib
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLtOneOfNotIsUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AwayOfInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyLocalPeriodRingsData
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.BKReal GlobalTheory.Prism Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.DiscEval GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_ring_no_zero_divisors : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (x : AK K), x ≠ 0 → ∀ y : GlobalTheory.AcrisK.BK K,
    toB K (ofA K x) * y = 0 → y = 0 := by
  first | exact @GlobalTheory.AcrisNZD.main | exact GlobalTheory.AcrisNZD.main | (intros; apply GlobalTheory.AcrisNZD.main <;> assumption)
