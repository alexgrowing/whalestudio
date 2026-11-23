import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizeBoundedBelowUnipotentRa
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.truncatedLeastLatticeSize_bounded_below_unipotentRadical : ∀ (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)) (x : I.GA), I.IsIsot W → ∃ c : ℝ, 0 < c ∧ ∀ m ∈ I.NA W, c ≤ tau1 I (m * x) := by
  first | exact @GlobalTheory.Dec.exists_pos_le_tau1_mul_of_mem_NA_of_isIsot | exact GlobalTheory.Dec.exists_pos_le_tau1_mul_of_mem_NA_of_isIsot | (intros; apply GlobalTheory.Dec.exists_pos_le_tau1_mul_of_mem_NA_of_isIsot <;> assumption)
