import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerSpaceDimFiniteGLLeOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
open GlobalTheory.FinGL Formalism.L2.DIV Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittakerSpaceDimFiniteGL_le_one : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (τ : Representation ℂ (GL (Fin r) F) V), τ.IsIrreducible → whDim ψ τ ≤ 1 := by
  first | exact @GlobalTheory.FinGL.GGFree.whDim_le_one | exact GlobalTheory.FinGL.GGFree.whDim_le_one | (intros; apply GlobalTheory.FinGL.GGFree.whDim_le_one <;> assumption)
