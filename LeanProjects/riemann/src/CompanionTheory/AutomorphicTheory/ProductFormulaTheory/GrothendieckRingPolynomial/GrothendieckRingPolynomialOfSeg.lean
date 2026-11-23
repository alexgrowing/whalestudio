import Mathlib
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.GrothOfThree
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.LUnlinkedIrrOfSeg
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.EmbeddingMiddleFactorTriple

namespace CompanionTheory.Groth

theorem grothendieckRingPolynomial_of_seg (hZ : GlobalTheory.Published.SegmentRepresentation) : GlobalTheory.Published.GrothendieckRingPolynomial :=
  groth_of_three hZ (fun k _ _ _ _ => CompanionTheory.Exh.lUnlinkedIrr_of_seg hZ k) fun k _ _ _ _ =>
    ⟨CompanionTheory.Exh.midP' k CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top, CompanionTheory.Exh.refineP' k,
      CompanionTheory.Exh.swapP' k (ClsOfF.comm_of (CompanionTheory.Exh.lUnlinkedIrr_of_seg hZ k))⟩

end CompanionTheory.Groth
