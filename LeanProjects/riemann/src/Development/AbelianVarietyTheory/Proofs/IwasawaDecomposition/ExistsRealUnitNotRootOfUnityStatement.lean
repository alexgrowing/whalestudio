import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealUnitNotRootOfUnity
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddSmulVecMulVecMulVec
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_real_unit_not_root_of_unity : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], 1 < Module.finrank ℚ E / 2 → ∃ u : (𝓞 E)ˣ, cc (u : E) = u ∧ ∀ n : ℕ, 0 < n → (u : E) ^ n ≠ 1 := by
  first | exact @GlobalTheory.UnipKill.exists_real_unit_infinite_order | exact GlobalTheory.UnipKill.exists_real_unit_infinite_order | (intros; apply GlobalTheory.UnipKill.exists_real_unit_infinite_order <;> assumption)
