import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductionFiniteLength
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_finite_length : GlobalTheory.Published.StandardFunctorsFiniteLength → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.JacquetFiniteLength k := by
  first | exact @GlobalTheory.JacquetBlocks.jacquetFiniteLength_of_standard | exact GlobalTheory.JacquetBlocks.jacquetFiniteLength_of_standard | (intros; apply GlobalTheory.JacquetBlocks.jacquetFiniteLength_of_standard <;> assumption)
