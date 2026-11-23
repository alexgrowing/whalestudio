import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeftMulUnitaryRepresentation
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToEndDApply
open GlobalTheory.LocFinIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.left_mul_unitary_representation : ∀ (G : Type) [Group G] [TopologicalSpace G] (K : Set G) (m : ℕ) (A : G → Matrix (Fin m) (Fin m) ℂ), A 1 = 1 → (∀ k ∈ K, ∀ k' ∈ K, A (k * k') = A k * A k') → (∀ k ∈ K, A k ∈ Matrix.unitaryGroup (Fin m) ℂ) → ContinuousOn A K → leftMul A 1 = 1 ∧ (∀ k ∈ K, ∀ k' ∈ K, leftMul A (k * k') = leftMul A k * leftMul A k') ∧ (∀ k ∈ K, ∀ v, ‖leftMul A k v‖ = ‖v‖) ∧ ∀ v, ContinuousOn (fun k => leftMul A k v) K := by
  first | exact @GlobalTheory.LeftMulRep.leftMul_spec | exact GlobalTheory.LeftMulRep.leftMul_spec | (intros; apply GlobalTheory.LeftMulRep.leftMul_spec <;> assumption)
