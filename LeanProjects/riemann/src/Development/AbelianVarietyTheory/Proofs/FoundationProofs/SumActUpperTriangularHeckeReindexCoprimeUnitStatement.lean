import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumActUpperTriangularHeckeReindexCoprimeUnit
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_act_upperTriangular_hecke_reindex_coprime_unit : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (c : X.Fn l), (∀ t : ℤ, X.act l !![1, t; 0, 1] c = c) → ∀ (q : ℕ) (e : ℤ), 0 < q → IsCoprime e (q : ℤ) → ∑ j ∈ Finset.range q, X.act l !![1, (j : ℤ) * e; 0, (q : ℤ)] c = ∑ j ∈ Finset.range q, X.act l !![1, (j : ℤ); 0, (q : ℤ)] c := by
  first | exact @GlobalTheory.KZ.Tower.sum_act_upper_mul_unit | exact GlobalTheory.KZ.Tower.sum_act_upper_mul_unit | (intros; apply GlobalTheory.KZ.Tower.sum_act_upper_mul_unit <;> assumption)
