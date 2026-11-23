import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointDataNonempty
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.point_data_nonempty : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p), (∀ i, (Y i).SplitFibres ∧ (Y i).N3) → ∀ (i : Idx H p) (C : Formalism.MainNotions.DIV.Cons.SCF p) (P : PointsOfFlagModel.PtC (Y i) C), Nonempty (DatAt (Y i) P) := by
  first | exact @GlobalTheory.DatAtAll.nonempty_datAt | exact GlobalTheory.DatAtAll.nonempty_datAt | (intros; apply GlobalTheory.DatAtAll.nonempty_datAt <;> assumption)
