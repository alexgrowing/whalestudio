import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetDepthLowerBoundSaturatedEvenType
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detDepth_lower_bound_saturated_even_type : ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → 3 ≤ p → ∀ (d h : ℕ), 0 < h → Even h → ∀ (ty : Fin d → ZMod h) (G : LogFGL v d), MuAction G p h ty → ∀ (j : ℕ), (∀ s : ZMod h, Odd s.val → (Finset.univ.filter fun a => ty a = s).card ≤ j) → ∀ (τ : ZMod h), Even τ.val → ∀ (i c : ℕ), 1 ≤ c → ∀ u : Fin i → Fin d → C, IsSatFrame v u → (∀ a e, ty e ≠ τ → u a e = 0) → ∃ cr : ℕ, cr ≤ i ∧ (cr : ℝ) ≤ j * (3 / 2 + Real.logb p c / 2) ∧ ((((i : ℝ) - cr) * c * p / ((p : ℝ) ^ 2 - 1) - (i : ℝ) ^ 2 * (Real.logb p c + 1) : ℝ) : EReal) ≤ detDepth G u c := by
  first | exact @GlobalTheory.DepthLow.detDepth_lower | exact GlobalTheory.DepthLow.detDepth_lower | (intros; apply GlobalTheory.DepthLow.detDepth_lower <;> assumption)
