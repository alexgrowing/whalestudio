import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentialOperatorDepthIntegralCoordinates
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentialOperatorDepth_integral_coordinates : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (i d c : ℕ) (G : LogFGL v d) (u : Fin i → Fin d → C) (Φ Ψ : Fin d → MvPowerSeries (Fin d) C), (∀ a, MvIsInt v (Φ a) ∧ constantCoeff (Φ a) = 0 ∧ MvIsInt v (Ψ a) ∧ constantCoeff (Ψ a) = 0) → (∀ a, subst Ψ (Φ a) = X a ∧ subst Φ (Ψ a) = X a) → ∀ (t : Fin d → MvPowerSeries (Fin i) C), (∀ a, constantCoeff (t a) = 0) → (∀ e, subst t (subst Φ (G.lg e)) = ∑ a, u a e • X a) → detDepth G u c = ⨅ f : {f : MvPowerSeries (Σ _ : Fin i, Fin d) C // MvIsInt v f}, toE (v (derivAt0 (detPow C i c) (subst (fun x : (Σ _ : Fin i, Fin d) => subst (fun a : Fin i => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) (t x.2)) f.1))) := by
  first | exact @GlobalTheory.FGDepth.Coord.depth_in_coords | exact GlobalTheory.FGDepth.Coord.depth_in_coords | (intros; apply GlobalTheory.FGDepth.Coord.depth_in_coords <;> assumption)
