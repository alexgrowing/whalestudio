import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatHalfSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTransport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeUniquenessOfCoveringStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainCoverOfPrintedResultsStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison GlobalTheory.ChainPts

namespace GlobalTheory.ChainPts

theorem latHalfSt (h₁ : GlobalTheory.CovTop.Hypotheses2) (h₂ : GlobalTheory.CovHt.HypothesesH) (h₃ : GlobalTheory.Published.PrismaticDieudonnePerfd)
    (h₄ : GlobalTheory.GroupBplus.GroupAllSt) : LatHalfSt :=
  latHalfSt_of (GlobalTheory.T.lattice_uniqueness_of_covering h₁) (GlobalTheory.T.chain_cover_of_hypotheses h₁ h₂ h₃ h₄)

end GlobalTheory.ChainPts

end
