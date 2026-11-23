import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Conclusion41OfHyp
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Formalism.SharpRestriction.LevelLetterCocycles.TypePrimeCongruences
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleRankR
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conclusion41_of_pAdicHodge : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.BhattScholzeIntegral → GlobalTheory.Published.FontaineBcris → GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ (C : ℝ) (CT : ℕ), 40 ≤ CT → 8 * (CT : ℝ) ≤ C → (∃ P : Pend D, admDZ P ∧ EigSpan P) → SumRepresentations.tie0 D → SumRepresentations.adm1 D → SumRepresentations.adm2 D → SumRepresentations.adm5 D → SumRepresentations.Conclusion41 D → SumRepresentations.ConclusionG5 D → SumRepresentations.ConclusionG6 D → ResidualIrreducibleRankR D → GlobalTheory.TypeLeaf.SerLoc D → TypePrimeCongruences.TypePrimeWildIdempotentChoice D → TieInePoly D → tieChi (D := D) → PairedCharacterCondition.aux₃ (D := D) C CT := by
  first | exact @GlobalTheory.ClosingLocalInputs.main | exact GlobalTheory.ClosingLocalInputs.main | (intros; apply GlobalTheory.ClosingLocalInputs.main <;> assumption)
