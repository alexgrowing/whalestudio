import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EvenOrderNormsOneAddFourMulOfNoRoot
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evenOrderNorms_one_add_four_mul_of_no_root : ∀ (K : Type) [Field K] (w : Valuation K ℤᵐ⁰) (ρ : K), (2 : K) ≠ 0 → w ρ ≤ 1 → (∀ x : K, w x ≤ 1 → w (x ^ 2 + x - ρ) = 1) → EvenNorms w (1 + 4 * ρ) := by
  first | exact @GlobalTheory.QNorm.evenNorms_one_add_four_mul | exact GlobalTheory.QNorm.evenNorms_one_add_four_mul | (intros; apply GlobalTheory.QNorm.evenNorms_one_add_four_mul <;> assumption)
