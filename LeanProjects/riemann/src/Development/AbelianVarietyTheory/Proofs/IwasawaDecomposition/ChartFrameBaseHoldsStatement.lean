import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartFrameBaseHolds
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankEqZeroIff
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.LocM GlobalTheory.LocM.Cht
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_frame_base_holds : GlobalTheory.LocM.Cht.FrameBaseSt := by
  first | exact @GlobalTheory.LocM.FrameBase.frameBase | exact GlobalTheory.LocM.FrameBase.frameBase | (intros; apply GlobalTheory.LocM.FrameBase.frameBase <;> assumption)
