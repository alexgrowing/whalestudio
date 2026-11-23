import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraicTowerKhatPadicSmulTorsionFree
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicTowerKhat_padic_smul_torsionFree : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], [IsAlgClosed Ω] → ∀ (c : ℤ_[l]) (x : X.Khat l), c ≠ 0 → c • x = 0 → x = 0 := by
  first | exact @GlobalTheory.KZ.H3.khat_torsionFree | exact GlobalTheory.KZ.H3.khat_torsionFree | (intros; apply GlobalTheory.KZ.H3.khat_torsionFree <;> assumption)
