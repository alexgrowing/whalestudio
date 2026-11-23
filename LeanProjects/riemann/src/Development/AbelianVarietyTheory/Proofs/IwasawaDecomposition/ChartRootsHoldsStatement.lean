import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartRootsHolds
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankEqZeroIff
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.LocM GlobalTheory.LocM.Cht
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_roots_holds : GlobalTheory.LocM.Cht.RootsSt := by
  first | exact @GlobalTheory.LocM.RootsPrescribe.roots | exact GlobalTheory.LocM.RootsPrescribe.roots | (intros; apply GlobalTheory.LocM.RootsPrescribe.roots <;> assumption)
