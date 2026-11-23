import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzTensorRightOperator
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTemperateGrowthElim

open GlobalTheory.SliceSchwartz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_tensor_right_operator : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (κ κ' κ₁' : Type)
    [Fintype κ] [Fintype κ'] [Fintype κ₁'] (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ),
    ∃ Q : SchwartzMap (κ ⊕ κ' → V) ℂ →L[ℂ] SchwartzMap (κ ⊕ κ₁' → V) ℂ,
      ∀ (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (s : κ ⊕ κ₁' → V), Q f s = P (sliceR f (s ∘ Sum.inl)) (s ∘ Sum.inr) := by
  first | exact @GlobalTheory.SliceOp.exists_tensor_clm | exact GlobalTheory.SliceOp.exists_tensor_clm | (intros; apply GlobalTheory.SliceOp.exists_tensor_clm <;> assumption)
