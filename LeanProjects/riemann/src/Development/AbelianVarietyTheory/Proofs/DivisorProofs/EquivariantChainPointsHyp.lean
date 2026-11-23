import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsBaseEqChain
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatHalfSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateOneOfPrintedResultsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalModelVerticalLettersSetupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeHalfOfPrintedResultsStatement

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison

namespace GlobalTheory.ChainPts

theorem htHalfSt_of_htOneSt (h : HTOneSt) : HTHalfSt := by
  intro D O hO p _ W hW jc hj z c
  haveI := isDiscreteValuationRing_V z.Z.i.c (Fact.out : p.Prime) hW
  obtain ⟨B₁, f₁, hB₁, hf₁, lw, oo, hP⟩ := h D O hO p W hW jc hj z c
  refine ⟨B₁, f₁, hB₁, hf₁, fun B g _ _ => ?_⟩
  obtain ⟨lw', oo', hP'⟩ := GlobalTheory.T.local_model_vertical_letters_setup z.Z B₁ B g _ (xAll O.S) lw oo hP
  exact ⟨lw', oo', by simpa only [Vert.Model.Hom.comp, Category.assoc] using hP'⟩

theorem eqChainSt_of_halves (hA : HTHalfSt) (hB : LatHalfSt) : EqChainSt := by
  intro D O hO p _ W hW jc hj z o c
  haveI := isDiscreteValuationRing_V z.Z.i.c (Fact.out : p.Prime) hW
  haveI := charP_residueField_of_mem_nonunits z.Z.i.c (Fact.out : p.Prime) hW
  obtain ⟨B₁, f₁, hB₁, hf₁, hAll⟩ := hA D O hO p W hW jc hj z c
  obtain ⟨B, g, hB, hg, hQ⟩ := hB D O hO p W hW jc hj z c o B₁ f₁ hB₁ hf₁
  obtain ⟨lw, oo, hP⟩ := hAll B g hB hg
  obtain ⟨Q, hlw, hoo⟩ := hQ lw oo hP
  refine ⟨B, g.comp f₁, Q, hB, ?_, hlw ▸ hP.2.1, hoo ▸ hP.2.2⟩
  unfold Vert.Model.Hom.relDim at *
  omega

theorem eqChainSt_of_groupAllSt : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → GlobalTheory.Published.PrismaticDieudonnePerfd →
    GlobalTheory.GroupBplus.GroupAllSt → EqChainSt := fun h₁ h₂ h₃ h₄ =>
  eqChainSt_of_halves (htHalfSt_of_htOneSt (GlobalTheory.T.hodge_tate_one_of_prismaticDieudonne h₁ h₂ h₃ h₄)) (GlobalTheory.T.lattice_half_of_hypotheses h₁ h₂ h₃ h₄)

end GlobalTheory.ChainPts

end
