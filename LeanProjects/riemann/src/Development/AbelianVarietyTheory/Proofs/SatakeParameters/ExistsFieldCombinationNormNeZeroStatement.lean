import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFieldCombinationNormNeZero
import Mathlib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_field_coeff_norm_sum_smul_ne_zero : ∀ {k B A : Type} [inst : Field k] [Infinite k] [inst_2 : CommRing B] [IsDomain B] [inst_4 : Algebra k B] [inst_5 : CommRing A] [inst_6 : Algebra B A] [Module.Free B A] [Module.Finite B A] {d : ℕ} (y : Fin d → A), (∃ x : Fin d → B, Algebra.norm B (∑ i, x i • y i) ≠ 0) → ∃ a : Fin d → k, Algebra.norm B (∑ i, algebraMap k B (a i) • y i) ≠ 0 := by
  first | exact @GlobalTheory.exists_field_combination_norm_ne_zero | exact GlobalTheory.exists_field_combination_norm_ne_zero | (intros; apply GlobalTheory.exists_field_combination_norm_ne_zero <;> assumption)
