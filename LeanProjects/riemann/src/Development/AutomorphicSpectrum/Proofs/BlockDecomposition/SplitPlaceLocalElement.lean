import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwCentSwTw
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.NormSplit

theorem thetaGL_eq_id_map {R : Type} [CommRing R] (a : ℕ) (c : R →+* R) (g : GL (Fin a) R) :
    thetaGL a c g = thetaGL a (RingHom.id _) (GeneralLinearGroup.map c g) := by
  ext i j
  rw [GlobalTheory.ThetaPull.thetaGL_apply, GlobalTheory.ThetaPull.thetaGL_apply, ← map_inv]
  rfl

theorem ratW_mul_thetaGL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (δ : GL (Fin n) E), IsSplitAt w →
    ratW n w δ * thetaGL n (RingHom.id _) (ratW n w (GeneralLinearGroup.map (IsCMField.complexConj E).toRingEquiv.toRingHom δ)) = locEl n w δ := by
  intro E _ _ _ n w δ hs
  unfold locEl
  rw [if_pos hs, map_mul]
  congr 1
  unfold thE
  rw [thetaGL_eq_id_map n (IsCMField.complexConj E).toRingEquiv.toRingHom δ]
  exact (GlobalTheory.ThetaPull.map_thetaGL (algebraMap E (w.adicCompletion E)) (RingHom.id _) (RingHom.id _) (fun _ => rfl) _).symm

end GlobalTheory.CompanionTheory.NormSplit

end
