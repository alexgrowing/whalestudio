import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothContinuousLimsupExtEq
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshExt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMoll
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_continuous_limsup_ext_eq : ∀ (D : ℕ) (Y : Type) [TopologicalSpace Y] (A : ReciprocityTheory.AnForm.M.FinHolAtlas D Y) (S : Set Y) (u : Y → ℝ), IsOpen S → A.SmoothOn S u → ContinuousOn u S ∧ ∀ y ∈ S, GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.limsupExt S u y = u y := by
  first | exact @GlobalTheory.Div.SmoothLimsup.main | exact GlobalTheory.Div.SmoothLimsup.main | (intros; apply GlobalTheory.Div.SmoothLimsup.main <;> assumption)
