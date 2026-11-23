import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiesAndInputsOfDualityEuler
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineAtAll
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineRestrictFiniteExtensionJumpsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrysOnCondOfEveryDatumStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoLocalAllOfTateDualityEulerCharStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremTbOfLocalBlochKatoDualityEulerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionExponentKillsInvariantsNoJumpZeroStatement
import Development.AutomorphicArithmetic.ResidueCharacters.LiftKOf
import Development.AutomorphicArithmetic.ResidueCharacters.InvariantsKilledOverCyclotomic
import Development.AutomorphicArithmetic.ResidueCharacters.TbKOf
import Development.AutomorphicArithmetic.ResidueCharacters.TwistK

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations

theorem UpperTheory.N.locAll_of (hbk : GlobalTheory.Published.BlochKatoLocal) (htd : Formalism.GaloisCohomology.LocalTateDualityK)
    (hec : Formalism.GaloisCohomology.LocalEulerCharK) (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (h54 : LiftingTheory.LiftTheoremAllCases D HW F 23 32 32)
    (hW : ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
      EmbeddingTypeJumps.WachHypothesisLocal (LocalSituation.sit D.loc HW l (D.locA l) K s LL h) ((F l).E K s LL h).tie) :
    UpperTheory.N.LiftK (D.loc l) ∧ UpperTheory.N.InvariantsKilledOverCyclotomic (D.loc l) ∧ UpperTheory.N.TBK (D.loc l) := by
  have hres : ElementDenominator.CrystallineRestrictionToExtension D.loc := GlobalTheory.T.crystalline_restrict_finite_extension_jumps D
  have hF := GlobalTheory.FontaineAll.fontaineAt_all D l
  obtain ⟨_J, hA⟩ := GlobalTheory.LocInputs.ties_and_inputs_of_duality_euler htd hec D HW F
  exact ⟨UpperTheory.N.liftK_of D HW F l h54 hres hF,
    UpperTheory.N.invariants_killed_over_cyclotomic_subfield_of_admissible D HW F l hW (fun K s LL h => GlobalTheory.T.torsion_exponent_kills_invariants_of_good hbk htd hec D HW F Cm l K s LL h) hres hF,
    UpperTheory.N.tbK_of D HW F l (GlobalTheory.T.theorem_tb_of_local_blochKato_duality_euler hbk htd hec D HW F Cm) (GlobalTheory.T.crysOnCond_of_every_datum D HW F) hW
      (UpperTheory.N.TwistK.tbe_all D HW F hA (GlobalTheory.T.blochKatoLocal_all_of_tateDuality_eulerChar hbk htd hec D) l) hres hF⟩
