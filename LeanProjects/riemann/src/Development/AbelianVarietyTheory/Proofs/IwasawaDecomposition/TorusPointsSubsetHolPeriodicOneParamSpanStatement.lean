import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorusPointsSubsetHolPeriodicOneParamSpan
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPerHolOne
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open scoped CategoryTheory.MonObj CategoryTheory.Obj
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.PeriodSpan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusPoints_subset_holPeriodicOneParamSpan : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (y : Sp ℂ ⟶ X) (E : TorusExtension ((Over.pullback y).obj G)), torusPts G y E ⊆ (perHolSub G y : Set (Over.mk y ⟶ G)) := by
  first | exact @GlobalTheory.PeriodSpan.torusPts_subset_perHolSub | exact GlobalTheory.PeriodSpan.torusPts_subset_perHolSub | (intros; apply GlobalTheory.PeriodSpan.torusPts_subset_perHolSub <;> assumption)
