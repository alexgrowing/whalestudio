import Mathlib
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.JacobianNonzeroSplittingOfProduct
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobian_nonzero_splitting_of_product : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O), FinHt B → ∀ (n : ℕ) (p q s : Matrix (Fin n) (Fin n) O) (N : ℕ), 1 ≤ N → s * (p * q) = (N : O) • (1 : Matrix (Fin n) (Fin n) O) → (p * q) * s = (N : O) • (1 : Matrix (Fin n) (Fin n) O) → IsDomain O → (N : O) ≠ 0 → jacM B (p * q) ≠ 0 → SplitKer B (p * q) → ∀ f : PS V n d, (∀ α ∈ kerM B q, shift B.G.F α f = f) → (kerM B (p * q)).Finite ∧ ∃ g : PS V n d, ∑ᶠ α ∈ kerM B (p * q), shift B.G.F α f = MvPowerSeries.C (((kerM B q).ncard : V) * jacM B p) * pullM B (p * q) g := by
  first | exact @GlobalTheory.PlaceInt.KerTrace.sum_shift_kerM_mul | exact GlobalTheory.PlaceInt.KerTrace.sum_shift_kerM_mul | (intros; apply GlobalTheory.PlaceInt.KerTrace.sum_shift_kerM_mul <;> assumption)
