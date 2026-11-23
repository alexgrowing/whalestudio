import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumRankOneIntegralRescaling
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddSmulVecMulVecMulVec
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_rank_one_integral_rescaling : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (d : ℕ) (ξ : Fin d → Fin N → E) (t : Fin d → E), (∀ j, cc (t j) = t j) → ∃ (k : ℕ) (ξ' : Fin d → Fin N → E) (s : Fin d → E), 0 < k ∧ (∀ j, ξ' j ∈ X.Λ) ∧ (∀ j, ∃ a : E, ξ' j = a • ξ j) ∧ (∀ j, cc (s j) = s j) ∧ (∀ j, IsIntegral ℤ (s j)) ∧ (k : E) • (∑ j, (t j * X.κ0) • rk1 X.Gm (ξ j) (ξ j)) = ∑ j, (X.m * s j * X.κ0) • rk1 X.Gm (ξ' j) (ξ' j) := by
  first | exact @GlobalTheory.UnipKill.scaleDecomp | exact GlobalTheory.UnipKill.scaleDecomp | (intros; apply GlobalTheory.UnipKill.scaleDecomp <;> assumption)
