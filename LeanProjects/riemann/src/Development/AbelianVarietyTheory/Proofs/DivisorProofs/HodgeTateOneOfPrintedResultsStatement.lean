import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateOneOfPublished
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatHalfSt
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison GlobalTheory.ChainPts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_one_of_prismaticDieudonne : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → GlobalTheory.Published.PrismaticDieudonnePerfd → GlobalTheory.GroupBplus.GroupAllSt → HTOneSt := by
  first | exact @GlobalTheory.ChainPts.htOneSt_of_prismaticDieudonne | exact GlobalTheory.ChainPts.htOneSt_of_prismaticDieudonne | (intros; apply GlobalTheory.ChainPts.htOneSt_of_prismaticDieudonne <;> assumption)
