import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BettiFunctionSubMemOfColumnsCongr
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bettiFunction_sub_mem_of_columns_congr : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime] (b : X.Fn l), b ∈ X.B N l w → ∀ (n : ℕ) (u v : Fin 2 → ℤ_[l]), (∀ i, u i - v i ∈ (idl l) ^ n) → b u - b v ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l)) := by
  first | exact @GlobalTheory.KZ.Tower.B_sub_mem | exact GlobalTheory.KZ.Tower.B_sub_mem | (intros; apply GlobalTheory.KZ.Tower.B_sub_mem <;> assumption)
