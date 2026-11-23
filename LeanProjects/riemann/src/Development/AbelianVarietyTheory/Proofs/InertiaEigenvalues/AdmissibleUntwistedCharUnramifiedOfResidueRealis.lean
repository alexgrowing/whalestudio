import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentOfIndepMod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClsEqHomModInertia
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleClassesPropsOfFlatCoefficient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSumsTwistsCharactersExpectedJumpsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleQuotientOfFullRepresentation
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.TopSteps

theorem admissibleUntwistedCharUnramified_of_residueRealisation {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (hT : Nonempty (LocTied l P AI)) (hR : ∀ S : TopSit P, S.Real) :
    GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleCharUnramified.AdmChiOneUnramified P := by
  intro K LL n r emb D Γ hst hgal h1 h2 h3 X _ _ _
  let S : TopSit P :=
    { K := K, LL := LL, n := n, r := r, nz := ⟨GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.letters_ne_zero hst⟩, emb := emb, D := D, Γ := Γ,
      hyp := ⟨hst, hgal, h1, h2, h3⟩ }
  have hcrys : S.CrysCalc := GlobalTheory.T.crystalline_sums_twists_characters_expected_jumps AI hT S
  have hcl : S.Closed := GlobalTheory.AdmClosure.admissible_closed S
  have hstd : S.StdAdm := StdAdm.stdAdm S hcrys hcl
  have hL : S.Lem0 (S.Γ.Wchi 1) := (GlobalTheory.AdmClasses.admissibleLocalSituation_admissible_classes S hcl hstd).2 1 le_rfl S.D.one_le_letterBlockLength
  have hb : S.ResBound (S.Γ.Wchi 1) 1 := (CharBound.resBound_chars S (hR S)).2 hL
  have hu : S.UnrAdm := GlobalTheory.UnramAdm.unramified_admissible S hcrys hcl hstd hL
  exact ChiOne.cls_eq_homModInertia S hL hb hu X

end GlobalTheory.TopSteps
