import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.Definitions.Divisors.GrNormCompCast
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultiplicityDifferentEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOpnOfSpecializes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupStructureOfPublishedInputsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivariantChainPointsHypStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainPointsOfEqualChainsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainPointsReadLieStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainPointsOmegaStableStatement

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.ChainPts

namespace GlobalTheory.MixedLocalChains

theorem hasChain_of_pts {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ} [Fact p.Prime] {hp : p.Prime}
    {W : ValuationSubring ℂ} {hW : (p : ℂ) ∈ W.nonunits} (z : AdmAt S κ hp hW) (jc : KW p →+* ℂ) (o : ℕ)
    (hd : GlobalTheory.ShFam.Pad.vDiff D.host.E p = 0) (h1 : HasChainPts z jc o) (h2 : ReadsLie z) (h3 : ReadsOm z) :
    HasChain z jc o :=
  fun c => (h1 c).imp fun B k => k.imp fun f k => k.imp fun _ k => ⟨k.1, k.2.1, fun τ =>
    ⟨(k.2.2 τ).1.1, (k.2.2 τ).2.1,
      h2 (dimFl D.what₂.Tau N) _ (fun i => .inl (jc.comp τ, i)) (xLie S jc τ) (letterOf_lie S jc τ)
        (xLie_initial S jc τ) (xLie_stepNorms S jc τ hd) c B f k.1 k.2.1 _ (k.2.2 τ).1,
      h3 (dimFl D.what₂.Tau N) _ (fun i => .inl (conjEmb (jc.comp τ), (Fin.rev i : Fin _))) (xOm S jc τ)
        (letterOf_om S jc τ) (xOm_initial S jc τ) (xOm_stepNorms S jc τ hd) c B f k.1 k.2.1 _ (k.2.2 τ).2⟩⟩

theorem chainSt_of_pts (h1 : ChainPtsSt) (h2 : ReadsLieSt) (h3 : ReadsOmSt) : ChainSt :=
  fun D O hO p _ h₂ hu hl W hW jc hj z o =>
    hasChain_of_pts z jc o ((GlobalTheory.ShFam.Pad.vDiff_spec D p).2.1 hu) (h1 D O hO p h₂ hu hl W hW jc hj z o)
      (h2 D O hO p W hW jc hj z) (h3 D O hO p W hW jc hj z)

theorem chainSt (hx : GlobalTheory.CovTop.HypothesesXH) (h2 : GlobalTheory.CovTop.Hypotheses2) (hH : GlobalTheory.CovHt.HypothesesH)
    (hP : GlobalTheory.Published.PrismaticDieudonnePerfd) : ChainSt :=
  chainSt_of_pts
    (GlobalTheory.T.chain_points_of_equal_chains (GlobalTheory.T.equivariant_chain_points_hyp h2 hH hP
      ((GlobalTheory.T.group_structure_of_published_inputs hx.ray hx.orth hx.dual hx.cube).all GlobalTheory.GroupBplus.genericSt)))
    GlobalTheory.T.chain_points_read_lie GlobalTheory.T.chain_points_omega_stable

end GlobalTheory.MixedLocalChains

end
