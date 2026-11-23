import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonDenominatorIsIntegral
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddSmulVecMulVecMulVec
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_denominator_isIntegral : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (f : Fin n → E), ∃ d : ℕ, 0 < d ∧ ∀ j, IsIntegral ℤ ((d : E) * f j) := by
  first | exact @GlobalTheory.exists_common_denominator | exact GlobalTheory.exists_common_denominator | (intros; apply GlobalTheory.exists_common_denominator <;> assumption)
