import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankBalancedIntBilinFormsEqOfFiniteIndex
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemBalBil
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_balancedIntBilinForms_eq_of_finite_index : ∀ {O : Type} [CommRing O] (bar : O → O) (X Y : Type) [AddCommGroup X] [Module O X] [Module.Free ℤ X] [Module.Finite ℤ X] [AddCommGroup Y] [Module O Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (f : Y →ₗ[O] X) (m : ℕ), 0 < m → Function.Injective f → (∀ x : X, m • x ∈ LinearMap.range f) → Module.finrank ℤ (GlobalTheory.BalRank.balBil bar Y) = Module.finrank ℤ (GlobalTheory.BalRank.balBil bar X) := by
  first | exact @GlobalTheory.BalRank.finrank_balBil_eq_of_finiteIndex | exact GlobalTheory.BalRank.finrank_balBil_eq_of_finiteIndex | (intros; apply GlobalTheory.BalRank.finrank_balBil_eq_of_finiteIndex <;> assumption)
