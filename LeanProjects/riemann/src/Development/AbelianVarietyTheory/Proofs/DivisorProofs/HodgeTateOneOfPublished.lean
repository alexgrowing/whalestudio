import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatHalfSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalModelWithPresentationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalModelLettersPresentationStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison GlobalTheory.ChainPts

namespace GlobalTheory.ChainPts

theorem htOneSt_of_prismaticDieudonne : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → GlobalTheory.Published.PrismaticDieudonnePerfd →
    GlobalTheory.GroupBplus.GroupAllSt → HTOneSt := by
  intro h1 h2 h3 h4 D O hO p _ W hW jc hj z
  haveI := isDiscreteValuationRing_V z.Z.i.c (Fact.out : p.Prime) hW
  intro c
  obtain ⟨B₁, f₁, hn, hr, oo, π, u, hπ, hu, hoo⟩ := GlobalTheory.T.exists_normal_model_with_presentation h1 h2 h3 h4 D O hO p W hW jc hj z c
  obtain ⟨lw, wl, hwl, hlw⟩ := GlobalTheory.T.local_model_letters_presentation z.Z (f₁.f ≫ (nmodel z.Z).compι c) (xAll O.S) oo π u hu hoo
  exact ⟨B₁, f₁, hn, hr, lw, oo, ⟨π, wl, hπ, hwl⟩, hlw, hoo⟩

end GlobalTheory.ChainPts

end
