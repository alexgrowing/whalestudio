import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvdUnitPowSubOne
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddSmulVecMulVecMulVec
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvd_unit_pow_sub_one : ∀ (E : Type) [Field E] [NumberField E] (u : (𝓞 E)ˣ) (M : 𝓞 E), M ≠ 0 → ∃ k : ℕ, 0 < k ∧ M ∣ ((u ^ k : (𝓞 E)ˣ) : 𝓞 E) - 1 := by
  first | exact @GlobalTheory.UnipKill.unit_pow_congr_one | exact GlobalTheory.UnipKill.unit_pow_congr_one | (intros; apply GlobalTheory.UnipKill.unit_pow_congr_one <;> assumption)
