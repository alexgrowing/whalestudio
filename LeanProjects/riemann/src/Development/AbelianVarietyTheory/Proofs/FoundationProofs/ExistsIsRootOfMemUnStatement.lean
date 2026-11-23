import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsRootOfMemUn
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isRoot_of_mem_Un_of_jHol : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) , JHol X → ∀ (m : ℕ), 0 < m → ∀ f ∈ X.Un m, ∃ a b : ℂ → ℂ, IsRoot X m f a b := by
  first | exact @GlobalTheory.KZ.H3.UnRoot.exists_isRoot_of_mem_Un | exact GlobalTheory.KZ.H3.UnRoot.exists_isRoot_of_mem_Un | (intros; apply GlobalTheory.KZ.H3.UnRoot.exists_isRoot_of_mem_Un <;> assumption)
