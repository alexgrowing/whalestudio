import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentOfIndepMod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantTwCoef
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleClassesPropsOfFlatCoefficient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSumsTwistsCharactersExpectedJumpsStatement

namespace GlobalTheory.TopSteps.CharVanish
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries

theorem cls_eq_zero {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P) (hC : S.CrysCalc) (hR : S.Real)
    (c : ℕ) (h2 : 2 ≤ c) (ht : c ≤ S.D.t) (X : Type) [AddCommGroup X] [Module S.O X] [Finite X] :
    S.cls (S.Γ.Wchi c) X = {0} := by
  have hcl : S.Closed := GlobalTheory.AdmClosure.admissible_closed S
  have hL : S.Lem0 (S.Γ.Wchi c) :=
    (GlobalTheory.AdmClasses.admissibleLocalSituation_admissible_classes S hcl (GlobalTheory.TopSteps.StdAdm.stdAdm S hC hcl)).2 c (by omega) ht
  exact GlobalTheory.TopSteps.CharAllCoef.main S c hL
    ((GlobalTheory.TopSteps.CharBound.resBound_chars S hR).1 c h2 ht hL) X

theorem stmt_of_real : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    Nonempty (LocTied l P AI) → (∀ S : TopSit P, S.Real) → GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleTwistedCharClasses.Stmt P := by
  intro l _ P AI hT hR K LL n r emb D Γ hyp c h2 ht X _ _ _
  have : NeZero n := ⟨GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.letters_ne_zero hyp.1⟩
  let S : TopSit P := ⟨K, LL, n, r, emb, D, Γ, hyp⟩
  exact cls_eq_zero S (GlobalTheory.T.crystalline_sums_twists_characters_expected_jumps AI hT S) (hR S) c h2 ht X

end GlobalTheory.TopSteps.CharVanish
