import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixIntegralOfAddCharTraceDual
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
open ValuativeRel GlobalTheory.SplitWeil Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_integral_of_addChar_trace_dual : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Y Y' : Type) [Fintype Y] [Fintype Y'] (ψk : AddChar k Circle), Continuous ψk → ψk ≠ 1 → ∀ x : Matrix Y Y' k, (∀ b : Matrix Y Y' k, (∀ u : Matrix Y Y' k, (∀ r q, u r q ∈ 𝒪[k]) → ψk (∑ r, ∑ q, b r q * u r q) = 1) → ψk (∑ r, ∑ q, b r q * x r q) = 1) → ∀ r q, x r q ∈ 𝒪[k] := by
  first | exact @GlobalTheory.CharDualMat.integral_of_dual | exact GlobalTheory.CharDualMat.integral_of_dual | (intros; apply GlobalTheory.CharDualMat.integral_of_dual <;> assumption)
