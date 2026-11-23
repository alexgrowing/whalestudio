import Mathlib
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FormalSeriesDescendsOfSplitKernelInvariant
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalSeries_descends_of_splitKernel_invariant : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O), FinHt B → ∀ (n : ℕ) (q q' : Matrix (Fin n) (Fin n) O) (N : ℕ), 1 ≤ N → q' * q = (N : O) • (1 : Matrix (Fin n) (Fin n) O) → jacM B q ≠ 0 → SplitKer B q → ∀ f : PS V n d, (∀ α ∈ kerM B q, shift B.G.F α f = f) → ∃ f', f = pullM B q f' := by
  first | exact @GlobalTheory.PlaceInt.descends_of_invariant | exact GlobalTheory.PlaceInt.descends_of_invariant | (intros; apply GlobalTheory.PlaceInt.descends_of_invariant <;> assumption)
