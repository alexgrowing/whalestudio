import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPointFlagInCellOfFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_genericPoint_flag_in_cell_of_frame : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ (z : X.X) (A : Mat m X.Fn), A ∈ E.S z → ∃ u : Cell m → Y.Fn, InCell E E' φ f A u (genericPoint Y.X) := by
  first | exact @GlobalTheory.FlagCell2.GenericCell.exists_inCell_genericPoint | exact GlobalTheory.FlagCell2.GenericCell.exists_inCell_genericPoint | (intros; apply GlobalTheory.FlagCell2.GenericCell.exists_inCell_genericPoint <;> assumption)
