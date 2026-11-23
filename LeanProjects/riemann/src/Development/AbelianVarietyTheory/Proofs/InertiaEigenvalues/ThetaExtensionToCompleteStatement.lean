import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaExtensionToComplete
import Mathlib
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLtOneOfNotIsUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AwayOfInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyLocalPeriodRingsData
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.BKReal GlobalTheory.Prism Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.DiscEval GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_extension_to_complete : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), ∃ ψ : GlobalTheory.AcrisK.BK K →+* ℂ_[l],
    ∀ x : AK K, ψ (toB K (ofA K x)) = ((thetaK K x : OC l) : ℂ_[l]) := by
  first | exact @GlobalTheory.AcrisK.exists_thetaB | exact GlobalTheory.AcrisK.exists_thetaB | (intros; apply GlobalTheory.AcrisK.exists_thetaB <;> assumption)
