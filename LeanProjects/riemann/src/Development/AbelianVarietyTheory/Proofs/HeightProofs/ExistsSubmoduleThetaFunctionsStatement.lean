import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSubmoduleThetaFunctions
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_submodule_thetaFunctions : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D), ∃ M : Submodule ℂ (WA V W → ℂ), ∀ f, f ∈ M ↔ IsThetaFun ψ V W f := by
  first | exact @GlobalTheory.FockCompare.exists_thetaSubmodule | exact GlobalTheory.FockCompare.exists_thetaSubmodule | (intros; apply GlobalTheory.FockCompare.exists_thetaSubmodule <;> assumption)
