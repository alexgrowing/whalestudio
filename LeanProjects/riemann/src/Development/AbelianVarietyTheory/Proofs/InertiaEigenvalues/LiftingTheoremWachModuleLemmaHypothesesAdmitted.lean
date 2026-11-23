import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingBounds
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.LocalInputFourteenOfLocal
import Formalism.SharpRestriction.LevelLetterCocycles.ExtensionInvariantClause
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeLaterClausesHoldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaOperatorSemisimpleOfConclusionsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictionCorestrictionH1fStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpsExactAdm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrPartAEveryRecord
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmulCocycle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineInequalityDcrisFiniteConcreteRings
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.LiftAdmitted

theorem all_admitted : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
    LiftingTheory.admitted D HW F Cm ∧ CrystallineLiftingBounds.admitted D HW F Cm := by
  intro D HW F Cm
  have hN : Formalism.MainNotions.DeltaInvariantLattices.DeltaInvariantNormBound D HW F Cm := GlobalTheory.T.wachLattice_laterClauses_hold D HW F Cm
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, c2, a, b, c, d, l3, -⟩ := hN
  have hU : HerrComplexNaturality.HerrExtensionUpToUnit D HW F := GlobalTheory.HerrExtUnit.main D HW F
  have h17 : LiftingTheory.adm17 D HW F := Formalism.MainNotions.UnusedSlot35.extension_clause D HW F ⟨p1, p8, hU⟩
  have h18 : LiftingTheory.adm18 D HW F := Formalism.MainNotions.UnusedSlot35.extension_invariant_clause D HW F ⟨p1, p8, p9, a, hU⟩
  have h19 : LiftingTheory.adm19 D HW F := GlobalTheory.T.gamma_operator_semisimple_of_conclusions D HW F Cm (GlobalTheory.T.wachLattice_laterClauses_hold D HW F Cm)
  have h20 : LiftingTheory.adm20 D HW F := GlobalTheory.T.restriction_corestriction_H1f D HW F
  have h21 : LiftingTheory.adm21 D HW F := class_map_naturality_of_herr D HW F (GlobalTheory.HerrFull.herr_part_a_every_record D HW F)
  have h22 : LiftingTheory.adm22 D HW F := fun l _ K LL =>
    (GlobalTheory.Per.FontaineBound.fontaineLe_of_tied l (D.loc l) (D.locA l) (D.locT l) K LL).1
  have h23 := GlobalTheory.jumps_exact_adm D HW F
  have hA : LiftingTheory.admitted D HW F Cm :=
    ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, c2, a, b, c, d, l3, h17, h18, h19, h20, h21, h22, h23.2⟩
  refine ⟨hA, ?_⟩
  exact ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, c2, a, b, c, d, l3, h17, h18, h19, h20, h21, h22, h23.1⟩

end GlobalTheory.LiftAdmitted
