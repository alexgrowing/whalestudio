import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.ropComm :
    UpperTheory.V.Cj.H.RopComm := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ T hT f hf F
  have hF := GlobalTheory.AutomorphicL2Unitary.isRepOp_Rop (Γ := Γ) (μ := μ) hf F
  have hTF := GlobalTheory.AutomorphicL2Unitary.isRepOp_Rop (Γ := Γ) (μ := μ) hf (T F)
  rw [hF.2, hTF.2]
  refine (T.integral_comp_comm hF.1).symm.trans ?_
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  show T (f g • (GlobalTheory.AutomorphicL2Unitary.R Γ μ g) F) = f g • (GlobalTheory.AutomorphicL2Unitary.R Γ μ g) (T F)
  rw [map_smul, hT g F]
