import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerateWhittakerDimParabolicInductionCuspidal
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
open GlobalTheory.FinGL Formalism.L2.DIV Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degenerateWhittakerDim_parabolicInduction_cuspidal : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V), IsCuspDatum b σ → ∀ j : ℕ, j < r ∨ j = 0 → whCut ψ (parInd b σ) j = splitDoublingNBlock b j * leviWh ψ b σ := by
  first | exact @GlobalTheory.FinGL.WhCutInd.degenerateWhittakerDim_parabolicInduction | exact GlobalTheory.FinGL.WhCutInd.degenerateWhittakerDim_parabolicInduction | (intros; apply GlobalTheory.FinGL.WhCutInd.degenerateWhittakerDim_parabolicInduction <;> assumption)
