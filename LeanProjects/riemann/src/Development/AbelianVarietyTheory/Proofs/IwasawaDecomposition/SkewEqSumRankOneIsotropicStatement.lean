import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SkewEqSumRankOneIsotropic
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddSmulVecMulVecMulVec
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skew_eq_sum_rank_one_isotropic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (G : Matrix (Fin N) (Fin N) E) (κ : E), (∀ a b, cc (G a b) = G b a) → G.det ≠ 0 → cc κ = -κ → κ ≠ 0 → ∀ (W : Submodule E (Fin N → E)), (∀ u ∈ W, ∀ v ∈ W, herm G u v = 0) → ∀ n : Matrix (Fin N) (Fin N) E, IsSkew G n → (∀ y, n.mulVec y ∈ W) → ∃ (d : ℕ) (ξ : Fin d → Fin N → E) (t : Fin d → E), (∀ j, ξ j ∈ W) ∧ (∀ j, cc (t j) = t j) ∧ n = ∑ j, (t j * κ) • rk1 G (ξ j) (ξ j) := by
  first | exact @GlobalTheory.UnipKill.skew_eq_sum_rk1 | exact GlobalTheory.UnipKill.skew_eq_sum_rk1 | (intros; apply GlobalTheory.UnipKill.skew_eq_sum_rk1 <;> assumption)
