import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedFactorEqProductAbove

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.ConjAtPlaces

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

abbrev cc : E ≃+* E := (IsCMField.complexConj E).toRingEquiv

def conjPerm : Equiv.Perm (HeightOneSpectrum (𝓞 E)) where
  toFun := conjSrc (cc E)
  invFun := conjSrc (cc E)
  left_inv := GlobalTheory.ThetaPull.conjSrc_conjSrc
  right_inv := GlobalTheory.ThetaPull.conjSrc_conjSrc

variable {E}

def conjCompl (w : HeightOneSpectrum (𝓞 E)) : (conjPerm E w).adicCompletion E ≃+* w.adicCompletion E :=
  RingEquiv.ofBijective (conjLoc (cc E) w)
    ⟨(conjLoc (cc E) w).injective, GlobalTheory.CuspRep.ParLaws.conjLoc_surjective (cc E) w⟩

theorem norm_conjCompl (w : HeightOneSpectrum (𝓞 E)) (y : (conjPerm E w).adicCompletion E) :
    ‖conjCompl w y‖ = ‖y‖ := by
  have key : ∀ (a b : NNReal) (ha : a ≠ 0) (hb : b ≠ 0), a = b → ∀ z,
      WithZeroMulInt.toNNReal ha z = WithZeroMulInt.toNNReal hb z := by
    rintro a _ ha hb rfl z
    rfl
  have hv : Valued.v (conjCompl w y) = Valued.v y := (conjLoc_spec (cc E) w).2.2 y
  have hN : (Ideal.absNorm w.asIdeal : NNReal) = Ideal.absNorm (conjPerm E w).asIdeal := by
    rw [show Ideal.absNorm (conjPerm E w).asIdeal = Ideal.absNorm w.asIdeal from
      GlobalTheory.UnrEuler.ConjFac.absNorm_conjSrc (cc E) w]
  rw [FinitePlace.norm_def, FinitePlace.norm_def, hv, key _ _ _ _ hN]

theorem conjPlaces : ConjPlaces := by
  intro E _ _ _
  refine ⟨fun v u => ?_, fun c => conjAd_algebraMap c, conjPerm E, conjCompl, norm_conjCompl, fun w u => ?_⟩
  · exact congrFun (GlobalTheory.ThetaPull.pInf_conjAd u) v
  · rfl

end GlobalTheory.CompanionTheory.ConjAtPlaces

end
