import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PairDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
open UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Lit.Geo.Pf.bddInt :
    UpperTheory.V.Lit.Geo.Pf.BddInt := by
  intro E _ _ _ a μ _ F hF ⟨C, hC⟩
  haveI := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  have h := GlobalTheory.CuspQuot.memL2_of_bound (μ := μ) hF.cont
    (GlobalTheory.CuspRep.CuspidalL2GL.leftInv_latticeGL hF.left hF.centre) hC
  exact ⟨h.2.integrable one_le_two, h⟩
