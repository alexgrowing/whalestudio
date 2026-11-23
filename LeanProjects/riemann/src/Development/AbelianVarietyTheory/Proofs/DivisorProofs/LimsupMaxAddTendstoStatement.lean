import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LimsupMaxAddTendsto
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshExt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMoll
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.limsup_max_add_tendsto : ∀ (α : Type) (l : Filter α) [l.NeBot] (c f : α → ℝ) (c₀ κ M : ℝ), Filter.Tendsto c l (nhds c₀) → (∀ᶠ t in l, f t ≤ M) → Filter.limsup (fun t => max (c t + f t) (-κ)) l = (max ((c₀ : EReal) + Filter.limsup (fun t => (f t : EReal)) l) ((-κ : ℝ) : EReal)).toReal := by
  first | exact @GlobalTheory.limsup_max_add_tendsto_eq_toReal | exact GlobalTheory.limsup_max_add_tendsto_eq_toReal | (intros; apply GlobalTheory.limsup_max_add_tendsto_eq_toReal <;> assumption)
