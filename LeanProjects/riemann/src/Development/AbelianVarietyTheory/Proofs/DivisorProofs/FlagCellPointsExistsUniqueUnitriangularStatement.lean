import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellPointsExistsUniqueUnitriangular
import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_cell_points_existsUnique_unitriangular : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ (A : Mat m X.Fn) (u : Cell m → Y.Fn), InCell E E' φ f A u (genericPoint Y.X) → ∀ (K : Type) [Field K] (x : Sp K ⟶ X.X), A ∈ E.S (x (IsLocalRing.closedPoint K)) → ∀ y₀ : Cell m → K, ∃! p : Sp K ⟶ Y.X, p ≫ f = x ∧ InCell E E' φ f A u (p (IsLocalRing.closedPoint K)) ∧ ∀ j, (ratOf Y).val p (u j) = y₀ j := by
  first | exact @GlobalTheory.FlagCell2.cell_points_existsUnique | exact GlobalTheory.FlagCell2.cell_points_existsUnique | (intros; apply GlobalTheory.FlagCell2.cell_points_existsUnique <;> assumption)
