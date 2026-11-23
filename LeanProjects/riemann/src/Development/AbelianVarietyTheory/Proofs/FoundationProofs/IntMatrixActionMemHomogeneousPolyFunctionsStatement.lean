import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntMatrixActionMemHomogeneousPolyFunctions
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intMatrixAction_mem_homogeneousPolyFunctions : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l w : ℕ) [Fact l.Prime] (m : Matrix (Fin 2) (Fin 2) ℤ), (∀ a ∈ X.A l, X.kmap l (X.sl (toGQ m)).toRingEquiv a ∈ X.A l) → ∀ b ∈ X.Pol l w, X.act l m b ∈ X.Pol l w := by
  first | exact @GlobalTheory.KZ.PolAct.act_mem_pol | exact GlobalTheory.KZ.PolAct.act_mem_pol | (intros; apply GlobalTheory.KZ.PolAct.act_mem_pol <;> assumption)
