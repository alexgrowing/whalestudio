import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockVectorsOfThetaDatumInjective
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.Chain GlobalTheory.CompactHowe Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVectorsOfThetaDatum_injective : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (M : DSModel V S) (M' : DSModel W S') (f : WO V W → ℂ), IsStdChar D ψ (-1) → IsInfFam θ → IsVacVec ψ θ M M' f → Function.Injective (ptOf ψ θ M M' f) := by
  first | exact @GlobalTheory.FockInj.ptOf_injective | exact GlobalTheory.FockInj.ptOf_injective | (intros; apply GlobalTheory.FockInj.ptOf_injective <;> assumption)
