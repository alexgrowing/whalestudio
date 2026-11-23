import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InnerMapEqConstMulProdInner
import Mathlib
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inner_multilinearMap_eq_mul_prod_inner : ∀ {ι : Type} [Fintype ι] {Xs : ι → Type} [∀ i, NormedAddCommGroup (Xs i)] [∀ i, InnerProductSpace ℂ (Xs i)] {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (f : MultilinearMap ℂ Xs E) (K : ℝ), (∀ x, ‖f x‖ ^ 2 = K * ∏ i, ‖x i‖ ^ 2) → ∀ x y, ⟪f x, f y⟫_ℂ = (K : ℂ) * ∏ i, ⟪x i, y i⟫_ℂ := by
  first | exact @GlobalTheory.MultilinearMap.inner_map_eq_const_mul_prod_inner | exact GlobalTheory.MultilinearMap.inner_map_eq_const_mul_prod_inner | (intros; apply GlobalTheory.MultilinearMap.inner_map_eq_const_mul_prod_inner <;> assumption)
