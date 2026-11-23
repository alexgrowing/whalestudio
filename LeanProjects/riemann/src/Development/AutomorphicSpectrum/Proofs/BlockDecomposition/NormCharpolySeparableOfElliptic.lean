import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwCentSwTw
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

namespace GlobalTheory.CompanionTheory.SepLocEl

theorem cj_algebraMap {E : Type} [Field E] [NumberField E] [IsCMField E] {w : Pl E} (hw : ¬ IsSplitAt w) (x : E) :
    GlobalTheory.BCT.cj w (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) := by
  have key : ∀ (v : Pl E) (_ : v = w) (f : v.adicCompletion E →+* w.adicCompletion E), Continuous f →
      (∀ k : E, f (algebraMap E _ k) = algebraMap E _ (GlobalTheory.SplitPts.conjE E k)) →
      GlobalTheory.BCT.cj w (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) := by
    rintro v rfl f hf h
    have hex : ∃ s : v.adicCompletion E →+* v.adicCompletion E, Continuous s ∧
        ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) := ⟨f, hf, h⟩
    rw [GlobalTheory.BCT.cj, dif_pos hex]
    exact hex.choose_spec.2 x
  exact key _ (GlobalTheory.BCT.GlobLev.conjSrc_eq_of_not_split hw) _
    (conjLoc_spec (GlobalTheory.SplitPts.conjE E) _).1 (conjLoc_spec (GlobalTheory.SplitPts.conjE E) _).2.1

theorem nrmL_locEl {E : Type} [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (δ : GL (Fin n) E) :
    nrmL n w (locEl n w δ) = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (δ * thE E n δ) := by
  by_cases h : IsSplitAt w
  · simp only [nrmL, locEl, if_pos h]
  · simp only [nrmL, locEl, if_neg h]
    rw [map_mul]
    congr 1
    exact (GlobalTheory.ThetaPull.map_thetaGL (algebraMap E (w.adicCompletion E)) _ (GlobalTheory.BCT.cj w)
      (fun x => (cj_algebraMap h x).symm) δ).symm

theorem separable_charpoly_nrmL_locEl : CjEx → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (δ : GL (Fin n) E), polE δ ∈ Ell E n →
    (nrmL n w (locEl n w δ)).val.charpoly.Separable := by
  intro _ E _ _ _ n w δ hδ
  rw [nrmL_locEl]
  have e : (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (δ * thE E n δ)).val =
      (δ * thE E n δ).val.map (algebraMap E (w.adicCompletion E)) := rfl
  rw [e, Matrix.charpoly_map]
  exact Polynomial.Separable.map hδ.2.2.1

end GlobalTheory.CompanionTheory.SepLocEl

end
