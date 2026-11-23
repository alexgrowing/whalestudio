import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndexMeasureIntegralEqOfFineSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint
open GlobalTheory.IdxInt
open scoped Pointwise Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indexMeasureIntegral_eq_of_fineSubgroup : ∀ {W : Type} [AddCommGroup W] (A B : AddSubgroup W) (φ : W → ℂ), Fine A φ B → cint A φ = (∑ᶠ c : W ⧸ B, φ c.out) / (B.relIndex A : ℂ) := by
  first | exact @GlobalTheory.IdxInt.cint_eq_of_fine | exact GlobalTheory.IdxInt.cint_eq_of_fine | (intros; apply GlobalTheory.IdxInt.cint_eq_of_fine <;> assumption)
