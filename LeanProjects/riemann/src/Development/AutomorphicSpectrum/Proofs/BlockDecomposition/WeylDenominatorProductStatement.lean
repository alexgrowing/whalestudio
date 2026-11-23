import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeylDenominatorProduct
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TZero
open Finset GlobalTheory.CompanionTheory.CoefId
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weyl_denominator_product : ∀ {n : ℕ} (z : Fin n → ℂ), (∀ a, z a ≠ 0) → (∏ a, ∏ b, (1 + z a / z b)) * (∏ a, z a) ^ (n - 1) = 2 ^ n * (∏ p ∈ prs n, (z p.1 + z p.2)) ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.CoefId.prod_one_add_div_mul_prod_pow | exact GlobalTheory.CompanionTheory.CoefId.prod_one_add_div_mul_prod_pow | (intros; apply GlobalTheory.CompanionTheory.CoefId.prod_one_add_div_mul_prod_pow <;> assumption)
