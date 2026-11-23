import Mathlib
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSymmetricTranslationUnitsEqKappaRatio
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_symmetricTranslationUnits_eq_kappa_ratio : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (K : Type) [Field K] [Algebra ℚ K] [Algebra V K] [IsFractionRing V K] (h : PS K 2 d) (w0 : O), B.IsCanonGauge K h → ∀ (Θ : PS V 3 d) (jo : PS V 1 d), IsTheta B K h w0 Θ → IsIota B K h w0 jo → ∀ (n : ℕ) (mu : Matrix (Fin n) (Fin n) O) (N : ℕ), Odd N → (∀ j k, ∑ i, star (mu i j) * mu i k = if j = k then (N : O) else 0) → ∀ κ : PS V n d, IsKappa B K h w0 mu N κ → ∀ α ∈ kerM B mu, ∀ u : Fin n → PS V 1 d, (∀ b, TrUnit B Θ jo N (α b) (u b)) → (∏ b, evV (n := n) ![pt V d b] (u b)) * shift B.G.F α κ = κ := by
  first | exact @GlobalTheory.PlaceInt.prod_trUnit_mul_shift_kappa | exact GlobalTheory.PlaceInt.prod_trUnit_mul_shift_kappa | (intros; apply GlobalTheory.PlaceInt.prod_trUnit_mul_shift_kappa <;> assumption)
