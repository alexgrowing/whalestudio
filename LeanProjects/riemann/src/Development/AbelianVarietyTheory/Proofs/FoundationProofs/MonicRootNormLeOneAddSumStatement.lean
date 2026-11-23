import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MonicRootNormLeOneAddSum
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_root_le_one_add_sum_norm_coeff : ∀ (n : ℕ) (s : Fin n → ℂ) (y : ℂ), y ^ n + ∑ j, s j * y ^ (j : ℕ) = 0 → ‖y‖ ≤ 1 + ∑ j, ‖s j‖ := by
  first | exact @GlobalTheory.monic_root_norm_le_one_add_sum | exact GlobalTheory.monic_root_norm_le_one_add_sum | (intros; apply GlobalTheory.monic_root_norm_le_one_add_sum <;> assumption)
