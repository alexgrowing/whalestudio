import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ContinuousOfHeisenbergLevelAndSmooth
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_of_heisenberg_level_and_smooth : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ), Continuous ψ → ∀ (V W : HSp D) (f : WA V W → ℂ), (∃ U : AddSubgroup (WA V W), IsOpen (U : Set (WA V W)) ∧ ∀ u ∈ U, u.map (infPart D) = 0 → Heisenberg₂ ψ V W u f = f) → Sm (iotaW σ V W) f → Continuous f := by
  first | exact @GlobalTheory.FockCompare.ThetaCont.continuous_of_level_of_smooth | exact GlobalTheory.FockCompare.ThetaCont.continuous_of_level_of_smooth | (intros; apply GlobalTheory.FockCompare.ThetaCont.continuous_of_level_of_smooth <;> assumption)
