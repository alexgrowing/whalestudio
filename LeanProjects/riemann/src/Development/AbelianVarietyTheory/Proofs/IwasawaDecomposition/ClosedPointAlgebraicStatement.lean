import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosedPointAlgebraic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_point_algebraic : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (x : Y.X), IsClosed ({x} : Set Y.X) → ArInt.IsAlgPt (M.j x) := by
  first | exact @GlobalTheory.TrueGeo.ClosedAlg.isAlgPt_of_isClosed | exact GlobalTheory.TrueGeo.ClosedAlg.isAlgPt_of_isClosed | (intros; apply GlobalTheory.TrueGeo.ClosedAlg.isAlgPt_of_isClosed <;> assumption)
