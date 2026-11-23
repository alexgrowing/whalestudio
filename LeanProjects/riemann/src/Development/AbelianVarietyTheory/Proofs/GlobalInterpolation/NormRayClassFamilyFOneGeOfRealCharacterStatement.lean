import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormRayClassFamilyFOneGeOfRealCharacter
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_rayClassFamily_F_one_ge_of_real_character : ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ), χ * χ = 1 → c / 𝓕.B ^ A ≤ ‖𝓕.F χ 1‖ := by
  first | exact @GlobalTheory.Hk.RealChar.norm_F_one_ge | exact GlobalTheory.Hk.RealChar.norm_F_one_ge | (intros; apply GlobalTheory.Hk.RealChar.norm_F_one_ge <;> assumption)
