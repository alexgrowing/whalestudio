import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingTheoremCHypothesesAdmittedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremCConst25OfHypothesesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFullFaithfulExactPsiStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OnePlaceAdmissibleOfGapConstantLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EigenvalueProductMapsLetterLatticeOfConclusionsAStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeLaterClausesHoldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpsExactAdm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBisRest
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem ramifiedCoefficientChains_prv_twenty_five :
    GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
      ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
        RamifiedCoefficientChains.aux₃ D HW F 25 := by
  intro hBK hTD hEC D HW F Cm
  have hadm := GlobalTheory.T.localLifting_theoremC_hypotheses_admitted hBK hTD hEC D HW F Cm
  have h23 : LiftingTheory.adm23 D HW F := (GlobalTheory.jumps_exact_adm D HW F).2
  have hC4 : LetterConditionGlobal D HW F := GlobalTheory.T.letterConditionGlobal_of_N1used D HW F Cm (GlobalTheory.T.wachLattice_laterClauses_hold D HW F Cm)
  have hH : ElementDenominator.HerrClassNaturalExtension D.loc D.locA HW F := GlobalTheory.AdmHerrLocal.main D HW F
  have h22 : CrystallineLiftingBounds.adm22 D HW F := GlobalTheory.FontaineIneq.one_place_admissible_of_gap_constant_le D HW F
  have hL : InvariantsGenerators.LitFont D HW F := GlobalTheory.T.fontaine_fullFaithful_exact_psi D HW F
  exact GlobalTheory.T.ramified_coefficient_chains_of_hypotheses D HW F Cm 10 23 32 32 h23 hC4 hH h22 hL hadm

end GlobalTheory
