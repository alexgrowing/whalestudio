import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerPadicCompletionMapEvalDependsOnLevel
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.towerPadicCompletionMap_eval_depends_on_level : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (a : X.Khat l) (n : ℕ), ∃ M0 : ℕ, 0 < M0 ∧ ∀ φ ψ : X.K ≃+* X.K, (∀ f : X.K, (∀ γ ∈ CongruenceSubgroup.Gamma M0, X.sl (ofSL γ) f = f) → φ f = ψ f) → AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l φ a) = AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l ψ a) := by
  first | exact @GlobalTheory.KZ.Tower.eval_kmap_levelRed | exact GlobalTheory.KZ.Tower.eval_kmap_levelRed | (intros; apply GlobalTheory.KZ.Tower.eval_kmap_levelRed <;> assumption)
