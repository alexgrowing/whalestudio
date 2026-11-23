import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Sl2CoprimeFactorizationUnique
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeLetterPreservesBasisSet
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.StabHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sl2_mul_eq_of_coprime_det_factorization : ∀ (a c : ℤ), IsCoprime a c → c ≠ 0 → ∀ (y y' β β' : Matrix (Fin 2) (Fin 2) ℤ), y.det = a → y'.det = a → β.det = c → β'.det = c → y * β = y' * β' → ∃ g : SL(2, ℤ), (g : Matrix (Fin 2) (Fin 2) ℤ) * β = β' := by
  first | exact @GlobalTheory.sl2_right_factor_of_coprime_factorizations | exact GlobalTheory.sl2_right_factor_of_coprime_factorizations | (intros; apply GlobalTheory.sl2_right_factor_of_coprime_factorizations <;> assumption)
