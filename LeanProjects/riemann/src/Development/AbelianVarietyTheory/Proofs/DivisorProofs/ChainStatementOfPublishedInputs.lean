import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasChainW
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.GrNormCompCast
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivariantChainPointsHypStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupStructureOfPublishedInputsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOpnOfSpecializes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainPointsReadLieStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainPointsOmegaStableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainPtsWStOfEqChainSt

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison
open GlobalTheory.ChainPts

namespace GlobalTheory.BundleChernComparison

theorem hasChainW_of_pts {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ} [Fact p.Prime]
    {hp : p.Prime} {W : ValuationSubring ℂ} {hW : (p : ℂ) ∈ W.nonunits} (z : AdmAt S κ hp hW) (jc : KW p →+* ℂ)
    (h1 : HasChainPtsW z) (h2 : ReadsLie z) (h3 : ReadsOm z) : HasChainW z jc :=
  have hI' : Initial fun i : Fin (D.R.f * N) => xAll S i.rev.rev := by
    simp only [Fin.rev_rev]
    exact xAll_initial S
  have hS' : StepNorms S.Dw p (fun i : Fin (D.R.f * N) => .inr (i.rev.rev : ℕ)) fun i => xAll S i.rev.rev := by
    simp only [Fin.rev_rev]
    exact xAll_stepNorms S p
  fun c => (h1 c).imp fun B k => k.imp fun f k => k.imp fun _ k => ⟨k.1, k.2.1, k.2.2.1.1, k.2.2.2.1,
    h2 (dimFl D.what₂.Tau N) (D.R.f * N) (fun k => .inr (k : ℕ)) (xAll S) (letterOf_whole S) (xAll_initial S)
      (xAll_stepNorms S p) c B f k.1 k.2.1 _ k.2.2.1,
    h3 (dimFl D.what₂.Tau N) (D.R.f * N) (fun k => .inr (k.rev : ℕ)) (fun k => xAll S k.rev)
      (fun k => letterOf_whole S k.rev) hI' hS' c B f k.1 k.2.1 _ k.2.2.2⟩

theorem chainWSt : GlobalTheory.CovTop.HypothesesXH → GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → GlobalTheory.Published.RegularAlteration →
    GlobalTheory.Published.ScholzeWeinsteinB → GlobalTheory.Published.PrismaticDieudonnePerfd → ChainWSt :=
  fun hx h2 hH _ _ hP D O hO p _ W hW jc hpin z =>
    hasChainW_of_pts z jc
      (GlobalTheory.ChainPts.Forget.chainPtsWSt_of_eqChainSt
        (GlobalTheory.T.equivariant_chain_points_hyp h2 hH hP
          (GlobalTheory.GroupBplus.GroupSt.all (GlobalTheory.T.group_structure_of_published_inputs hx.ray hx.orth hx.dual hx.cube) GlobalTheory.GroupBplus.genericSt))
        D O hO p W hW jc hpin z)
      (GlobalTheory.T.chain_points_read_lie D O hO p W hW jc hpin z) (GlobalTheory.T.chain_points_omega_stable D O hO p W hW jc hpin z)

end GlobalTheory.BundleChernComparison

end
