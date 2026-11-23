import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTypicalCurveBasisAdaptedToSaturatedFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_typicalCurve_basis_adapted_to_saturated_frame : ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → ∀ (d h : ℕ), 0 < h → ∀ (ty : Fin d → ZMod h) (G : LogFGL v d), MuAction G p h ty → ∀ (τ : ZMod h) (j i : ℕ), (Finset.univ.filter fun a => ty a = τ + 1).card ≤ j → ∀ u : Fin i → Fin d → C, IsSatFrame v u → (∀ a e, ty e ≠ τ → u a e = 0) → ∃ (γ : Fin d → Fin d → PowerSeries C) (r : Fin i ↪ Fin d) (g : Matrix (Fin i) (Fin i) C), IsBasis G p ty γ ∧ (∀ a b, IsIntV v (g a b)) ∧ v g.det = 0 ∧ (∀ a, tangent (γ (r a)) = ∑ a', g a a' • u a') ∧ ∀ a : Fin i, j ≤ a.val → G.lc p (γ (r a)) 1 = 0 := by
  first | exact @GlobalTheory.FGDepth.exists_basis_adapted_frame | exact GlobalTheory.FGDepth.exists_basis_adapted_frame | (intros; apply GlobalTheory.FGDepth.exists_basis_adapted_frame <;> assumption)
