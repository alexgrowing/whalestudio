import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJointHighest
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EabIsKCInr
open MvPolynomial Formalism.BasicNotions.TH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_highest_weight_vector_alt : ∀ (P Q R S : ℕ) (N : Submodule ℂ (Formalism.BasicNotions.TH.Pol P Q R S)), FiniteDimensional ℂ N → N ≠ ⊥ → (∀ (c d : Fin R), ∀ w ∈ N, GlobalTheory.Capelli.rowOp ℂ (GlobalTheory.LowIrr.zR P Q R S) c d w ∈ N) → (∀ (c d : Fin S), ∀ w ∈ N, GlobalTheory.Capelli.rowOp ℂ (GlobalTheory.LowIrr.yS P Q R S) c d w ∈ N) → ∃ v ∈ N, v ≠ 0 ∧ (∀ c d : Fin R, c < d → GlobalTheory.Capelli.rowOp ℂ (GlobalTheory.LowIrr.zR P Q R S) c d v = 0) ∧ (∃ α : Fin R → ℂ, ∀ c, GlobalTheory.Capelli.rowOp ℂ (GlobalTheory.LowIrr.zR P Q R S) c c v = α c • v) ∧ (∀ c d : Fin S, c < d → GlobalTheory.Capelli.rowOp ℂ (GlobalTheory.LowIrr.yS P Q R S) c d v = 0) ∧ (∃ β : Fin S → ℂ, ∀ d, GlobalTheory.Capelli.rowOp ℂ (GlobalTheory.LowIrr.yS P Q R S) d d v = β d • v) := by
  first | exact @GlobalTheory.LowIrr.exists_joint_highest | exact GlobalTheory.LowIrr.exists_joint_highest | (intros; apply GlobalTheory.LowIrr.exists_joint_highest <;> assumption)
