import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Formalism.SharpRestriction.LevelLetterCocycles.TypePrimeCongruences
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleRankR
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConclusionOfLocalConditionsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallinePeriodBoundAllConstantGeFortyStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremTbOfLocalBlochKatoDualityEulerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoLocalAllOfTateDualityEulerCharStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalAbsorptionLengthBoundOfBlochKatoStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualRepSpansMatrixAlgebraOfGoodPoint
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LemmaOpenOfIntegrality
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

namespace GlobalTheory.ClosingLocalInputs

theorem galoisFamilyConditions_of_sumRepresentations (D : D7) (h41 : SumRepresentations.Conclusion41 D) : GaloisFamilyConditions (D := D) :=
  fun i r hr => (h41 i).2.2 r hr

theorem main : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.BhattScholzeIntegral → GlobalTheory.Published.FontaineBcris →
    GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
    ∀ (C : ℝ) (CT : ℕ), 40 ≤ CT → 8 * (CT : ℝ) ≤ C → (∃ P : Pend D, admDZ P ∧ EigSpan P) →
    SumRepresentations.tie0 D → SumRepresentations.adm1 D → SumRepresentations.adm2 D → SumRepresentations.adm5 D → SumRepresentations.Conclusion41 D → SumRepresentations.ConclusionG5 D → SumRepresentations.ConclusionG6 D →
    ResidualIrreducibleRankR D → GlobalTheory.TypeLeaf.SerLoc D → TypePrimeCongruences.TypePrimeWildIdempotentChoice D → TieInePoly D → tieChi (D := D) →
    PairedCharacterCondition.aux₃ (D := D) C CT := by
  intro hGAR hBS hFB hBKL hLTD hLEC D HW F Cm C CT hCT hC hP htie0 hadm1 hadm2 hadm5 h41 hG5 hG6 hN9 hSer hO
    hIne hChi
  obtain ⟨P, hDZ, hEig⟩ := hP
  have hT : admT (D := D) CT := GlobalTheory.T.crystallinePeriodBound_all_constant_ge_forty hBS hFB hBKL hLTD hLEC D HW F Cm CT hCT
  have hLOC : LocalPushoutProposition (D := D) := GlobalTheory.T.local_absorption_length_bound_of_blochKato hBKL hLTD hLEC D HW F Cm
  have hRbar : ResidualAbsIrreducible (D := D) := GlobalTheory.Pass.residualRep_spans_matrixAlgebra_of_goodPoint D hN9
  have hN5g : TypePrimeChoiceLemmas (D := D) := GlobalTheory.supplier_type_prime_all D ⟨hadm5, h41, hN9, hO⟩
  have hTB : admTB (D := D) HW F := GlobalTheory.T.theorem_tb_of_local_blochKato_duality_euler hBKL hLTD hLEC D HW F Cm
  have hBK : admBK (D := D) := GlobalTheory.T.blochKatoLocal_all_of_tateDuality_eulerChar hBKL hLTD hLEC D
  exact GlobalTheory.T.conclusion_of_local_conditions hGAR D P HW F C CT hC hadm5 hEig hIne hT hLOC hRbar hN5g hDZ
    (galoisFamilyConditions_of_sumRepresentations D h41) hG5 hG6 hSer hTB hBK hadm1 hadm2 htie0 hChi

end GlobalTheory.ClosingLocalInputs
