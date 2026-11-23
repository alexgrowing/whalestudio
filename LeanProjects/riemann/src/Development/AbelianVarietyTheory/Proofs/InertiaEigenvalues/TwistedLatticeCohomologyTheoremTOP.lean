import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JSmul
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPullBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleClassesPropsOfFlatCoefficient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToAmbCoefH1EqCoefAmbToAmb
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIndependentAdmissibleCocyclesResidue
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSumsTwistsCharactersExpectedJumps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteClassesSubsetAdmissibleOfGoodO
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowSmulEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VanishOfLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinsumCountNeg
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StrictnessOfTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPresTensor
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsModThOfPres
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StmtOfReal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleUntwistedCharUnramifiedOfResidueRealis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeUsedPropertiesOfAdmittedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExactLocalConditionsTopCoreStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH1LocalEulerFormulaStatement

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
open GlobalTheory.PhiGam GlobalTheory.Models
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.TopBridge

theorem freeH_of_vanish_euler : Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P), S.Vanish → S.FreeH := by
  intro heul l _ P S hV
  obtain ⟨hs, ht, -, -, -⟩ := S.hyp
  obtain ⟨hDVR, -, -, hA, hF, hFr⟩ := GlobalTheory.CoefInt.integers_laws l S.LL
  haveI := hDVR
  haveI := hFr
  exact GlobalTheory.FreeCoh.free_and_tensIso_gal S.Γ hs.2.2.2.2.2 hA hF
    (GlobalTheory.LocalIntegers.isOpen_integers l S.LL)
    (fun U hU => GlobalTheory.FreeCoh.pow_mul_mem_nhds S.LL S.Γ.lam hs.2.2.2.2.2 U hU)
    ht.2.2.1.1 (GlobalTheory.AdmClasses.not_isUnit_integers l S.LL) hV.1 hV.2 ht.1 hs.2.2.1
    (fun M _ _ _ π hlm hlc h0 h2 => GlobalTheory.T.card_H1_local_euler_formula heul l S.K S.O M π hlm hlc h0 h2)

theorem stmtAt_of_real (hdual : Formalism.GaloisCohomology.LocalTateDualityK) (heul : Formalism.GaloisCohomology.LocalEulerCharK)
    {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (htied : Nonempty (LocTied l P AI))
    (hreal : ∀ S : TopSit P, S.Real)
    (hbk : ∀ K LL : FinExt l, CaseA K LL → tableLineDegreeTwo.BlochKatoJumpDimension (P.PD K) (LL := ↥LL.1) (O := ↥(OL LL)) (IK K)) :
    GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.ErrorExponentStatement P := by
  intro K LL n r _ emb D Γ hs ht h1 h2 h3
  let S : TopSit P := ⟨K, LL, n, r, emb, D, Γ, ⟨hs, ht, h1, h2, h3⟩⟩
  have hCC : S.CrysCalc := GlobalTheory.TopSteps.CrysRules.crysCalc AI htied S
  have hR : S.Real := hreal S
  have hV : S.Vanish := GlobalTheory.TopVanish.vanish_of_real hdual S hR
  have hF : S.FreeH := freeH_of_vanish_euler heul S hV
  have hCl : S.Closed := GlobalTheory.AdmClosure.admissible_closed S
  have hStd : S.StdAdm := GlobalTheory.TopSteps.StdAdm.stdAdm S hCC hCl
  have hL0 : S.Lem0 S.Γ.W₀ := (GlobalTheory.AdmClasses.admissibleLocalSituation_admissible_classes S hCl hStd).1
  have hFS : S.FSummand :=
    GlobalTheory.TopSteps.FinSummandJumps.fSummand S (hbk K LL hs.2.1) hCC hV hF
  have hFA : S.FinAdm :=
    GlobalTheory.FiniteAdm.finAdm S hCC (GlobalTheory.FontaineExtensionCriteria.extCrys_of_tied P AI htied) hCl hStd hL0
  have hPsi : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.LemmaPsi := GlobalTheory.PsiShiftProof.lemmaPsi
  have hRB : S.ResBound S.Γ.W₀ S.D.dsum := GlobalTheory.ResidueBound.resBound_dsum hPsi S hR hL0
  refine ⟨hV.1, hV.2, hF.1, hFS, fun X _ _ _ => ⟨hF.2 X, ?_⟩⟩
  exact GlobalTheory.AdmFinite.cls_eq_H1fX S hL0 hF hFS hFA hRB X

theorem twistedLatticeCohomology_theoremTOP : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
    tableLineDegreeTwo.Stmt D HW F Cm := by
  intro D HW F Cm hA l _ K LL hK lam hlam
  have htied : Nonempty (LocTied l (D.loc l) (D.locA l)) := ⟨D.locT l⟩
  have h18 := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h19 := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hreal : ∀ S : TopSit (D.loc l), S.Real := fun S =>
    GlobalTheory.BasePairs.real_of_presented (D.locA l) (HW l) (F l) S
      (GlobalTheory.RedFun.realD (D.locA l) (HW l) (F l) S)
      (GlobalTheory.T.wachLattice_usedProperties_of_admitted D HW F Cm hA l S.K S.LL S.hyp.1.2.1)
      (GlobalTheory.TopSteps.CrysRules.crysCalc (D.locA l) htied S)
  exact GlobalTheory.T.exactLocalConditions_topCore (D.loc l) (D.locA l) htied (HW l)
    (stmtAt_of_real h18.1 h18.2 (D.loc l) (D.locA l) htied hreal (fun K' LL' hc => h19 l K' LL' hc))
    (GlobalTheory.TopSteps.CharVanish.stmt_of_real (D.loc l) (D.locA l) htied hreal)
    (GlobalTheory.TopSteps.admissibleUntwistedCharUnramified_of_residueRealisation (D.loc l) (D.locA l) htied hreal)
    K LL hK lam hlam

end GlobalTheory.TopBridge
