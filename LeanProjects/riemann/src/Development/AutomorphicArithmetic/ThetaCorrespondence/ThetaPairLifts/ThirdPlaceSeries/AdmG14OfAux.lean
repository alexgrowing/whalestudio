import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Conclusion41OfHyp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalGlobalCompatibility
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LemmaOpenOfIntegrality
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConclusionOfAdmissiblesStatement

set_option synthInstance.maxHeartbeats 200000

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules
namespace GlobalTheory.ClosingLocalInputs
theorem galoisFamilyConditions_of_sumRepresentations_alt (D : D7) (h41 : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D) : _root_.Formalism.MainNotions.PairedCharacterCondition.GaloisFamilyConditions' (D := D) :=
  fun i r hr => (h41 i).2.2 r hr
theorem main_alt_alt : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.BhattScholzeIntegral → GlobalTheory.Published.FontaineBcris →
    GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
    ∀ (C : ℝ) (CT : ℕ), 40 ≤ CT → 8 * (CT : ℝ) ≤ C → (∃ P : Pend D, admDZ P ∧ EigSpan P) →
    SumRepresentations.tie0 D → SumRepresentations.adm1 D → _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → SumRepresentations.adm5 D → _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → SumRepresentations.ConclusionG5 D → SumRepresentations.ConclusionG6 D →
    ResidualIrreducibleRankR D → GlobalTheory.TypeLeaf.SerLoc D → TypePrimeCongruences.TypePrimeWildIdempotentChoice D → TieInePoly D → tieChi (D := D) →
    _root_.Formalism.MainNotions.PairedCharacterCondition.PairedCharacterConditionAlt (D := D) C CT := by
  intro hGAR hBS hFB hBKL hLTD hLEC D HW F Cm C CT hCT hC hP htie0 hadm1 hadm2 hadm5 h41 hG5 hG6 hN9 hSer hO
    hIne hChi
  obtain ⟨P, hDZ, hEig⟩ := hP
  have hT : admT (D := D) CT := GlobalTheory.T.crystallinePeriodBound_all_constant_ge_forty hBS hFB hBKL hLTD hLEC D HW F Cm CT hCT
  have hLOC : LocalPushoutProposition (D := D) := GlobalTheory.T.local_absorption_length_bound_of_blochKato hBKL hLTD hLEC D HW F Cm
  have hRbar : ResidualAbsIrreducible (D := D) := GlobalTheory.Pass.residualRep_spans_matrixAlgebra_of_goodPoint D hN9
  have hN5g : TypePrimeChoiceLemmas (D := D) := _root_.GlobalTheory.typePrimeCongruences_forall D ⟨hadm5, h41, hN9, hO⟩
  have hTB : admTB (D := D) HW F := GlobalTheory.T.theorem_tb_of_local_blochKato_duality_euler hBKL hLTD hLEC D HW F Cm
  have hBK : admBK (D := D) := GlobalTheory.T.blochKatoLocal_all_of_tateDuality_eulerChar hBKL hLTD hLEC D
  exact _root_.GlobalTheory.T.admT_of_artin_reciprocity_and_local_conditions hGAR D P HW F C CT hC hadm5 hEig hIne hT hLOC hRbar hN5g hDZ
    (_root_.GlobalTheory.ClosingLocalInputs.galoisFamilyConditions_of_sumRepresentations_alt D h41) hG5 hG6 hSer hTB hBK hadm1 hadm2 htie0 hChi
end GlobalTheory.ClosingLocalInputs
end
