import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBoundedContinuousCuspidalAutomorphicZeroAddSmu
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumLieCoord
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBoundedContinuousCuspidalAutomorphic_zero_add_smul : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), IsBCC (0 : GA E a → ℂ) ∧
    ∀ (c : ℂ) (F G : GA E a → ℂ), IsBCC F → IsBCC G → IsBCC (c • F + G) := by
  first | exact @GlobalTheory.JSW.isBCC_zero_and_add | exact GlobalTheory.JSW.isBCC_zero_and_add | (intros; apply GlobalTheory.JSW.isBCC_zero_and_add <;> assumption)
