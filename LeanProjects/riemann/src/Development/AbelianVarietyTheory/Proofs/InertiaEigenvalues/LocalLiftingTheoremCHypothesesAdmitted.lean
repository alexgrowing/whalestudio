import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Formalism.SharpRestriction.LevelLetterCocycles.HerrClassFieldOfNorms
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.HerrDescriptionH1OfHerr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrPartAEveryRecord
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrExtensionClassFormula
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineDcrisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoDimFormulaAllLocalSituationsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fGeneratorsAllStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoCrystallineExtensionCriterionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fGenerationUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeLaterClausesHoldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaSubOneDivUniformiserAtLetterOfConclusionsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConstantsFromAdmittedLocalGaloisStatementsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleLocalConclusionsUsedFormsStatement
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.TheoremCAdm

theorem admissible_ranks_of_CMDatum : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
      RamifiedCoefficientChains.admitted D HW F Cm 10 23 32 32 := by
  intro hBK hTD hEC D HW F Cm
  have hU := (GlobalTheory.T.wachModuleLocalConclusions_usedForms D HW F Cm).1
  have h54 := GlobalTheory.T.localConstants_from_admitted_local_Galois_statements hBK hTD hEC D HW F Cm
  have h6a := GlobalTheory.HerrFull.herr_part_a_every_record D HW F
  exact ⟨hU.1, hU.2.1, hU.2.2.1, hU.2.2.2,
    RamifiedCoefficientChains.sizes_bound_of_log_estimates D HW F h54, RamifiedCoefficientChains.restriction_dimension_of_division D HW F h54, RamifiedCoefficientChains.level_tools_of_admitted D HW F h54, RamifiedCoefficientChains.lemma_M_prime_hypothesis D HW F h54,
    RamifiedCoefficientChains.crystalline_lift_of_theorem_c D HW F h54, RamifiedCoefficientChains.lifting_bounds_of_theorem_c D HW F h54,
    GlobalTheory.T.ramifiedCoefficientChains_adm11 D, GlobalTheory.T.blochKato_dimFormula_all_localSituations D, GlobalTheory.T.ramifiedCoefficientChains_adm13 D,
    Formalism.MainNotions.N.herr_description_H1_of_herr D HW F h6a, GlobalTheory.T.blochKato_crystalline_extension_criterion D,
    GlobalTheory.HerrExtClass.herr_extension_class_formula D HW F,
    Formalism.MainNotions.HerrComplexNaturality.herr_naturality_theorem_holds D HW F h6a,
    GlobalTheory.T.gamma_sub_one_div_uniformiser_at_letter_of_conclusions D HW F Cm (GlobalTheory.T.wachLattice_laterClauses_hold D HW F Cm),
    GlobalTheory.T.h1fGeneratorBoundAll_loc D⟩

end GlobalTheory.TheoremCAdm
