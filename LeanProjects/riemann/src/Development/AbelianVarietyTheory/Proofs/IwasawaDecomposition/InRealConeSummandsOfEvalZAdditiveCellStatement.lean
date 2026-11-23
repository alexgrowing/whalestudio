import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSummandsOfEvalZAdditiveCell
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkValEqZeroOrOne
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inRealCone_summands_of_evalZ_additive_cell : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ → ∀ (k : ℕ) (u : Fin k → LinearMap.BilinForm ℤ X), (∀ j, u j ∈ balForms bar X) → (∀ j y, 0 ≤ u j y y) → InRCone γ (∑ j, u j) → ψ.evalZ (∑ j, u j) ≤ ∑ j, ψ.evalZ (u j) → ∀ j, InRCone γ (u j) := by
  first | exact @GlobalTheory.PolFan.Mark.inRCone_of_evalZ_sum_le | exact GlobalTheory.PolFan.Mark.inRCone_of_evalZ_sum_le | (intros; apply GlobalTheory.PolFan.Mark.inRCone_of_evalZ_sum_le <;> assumption)
