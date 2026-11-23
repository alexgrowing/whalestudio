import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierGLBlockUnitIndicator
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partialFourierGLBlock_unitIndicator : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → fourG M ψ (unitG r F) = unitG r F := by
  first | exact @GlobalTheory.JR.fourG_unitG | exact GlobalTheory.JR.fourG_unitG | (intros; apply GlobalTheory.JR.fourG_unitG <;> assumption)
