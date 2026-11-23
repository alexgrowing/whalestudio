import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValAtOfUnder

noncomputable section

open scoped TensorProduct NNReal nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnrEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

namespace GlobalTheory.UnrTate

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem count_spanSingleton_eq (w : HeightOneSpectrum (𝓞 E)) {x : E} (hx : x ≠ 0) :
    FractionalIdeal.count E w (FractionalIdeal.spanSingleton (𝓞 E)⁰ x) = -WithZero.log (w.valuation E x) := by
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (𝓞 E)⁰ x
  have hs : (s : 𝓞 E) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have hr : r ≠ 0 := by
    rintro rfl
    exact hx (by simp)
  have hspan : ∀ {t : 𝓞 E}, t ≠ 0 → FractionalIdeal.count E w
      (FractionalIdeal.spanSingleton (𝓞 E)⁰ (algebraMap (𝓞 E) E t)) = -WithZero.log (w.valuation E (algebraMap (𝓞 E) E t)) := by
    intro t ht
    rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe E w
      (by rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]),
      HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg _ ht, WithZero.log_exp,
      neg_neg]
  have hs' : algebraMap (𝓞 E) E s ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hs
  have e : IsLocalization.mk' E r s * algebraMap (𝓞 E) E s = algebraMap (𝓞 E) E r :=
    IsLocalization.mk'_spec E r s
  have e2 := congrArg (FractionalIdeal.count E w) (congrArg (FractionalIdeal.spanSingleton (𝓞 E)⁰) e)
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.count_mul E w
    ((FractionalIdeal.spanSingleton_ne_zero_iff).mpr hx) ((FractionalIdeal.spanSingleton_ne_zero_iff).mpr hs'),
    hspan hs, hspan hr] at e2
  have e3 := congrArg (w.valuation E) e
  rw [map_mul] at e3
  have hv1 : w.valuation E (algebraMap (𝓞 E) E s) ≠ 0 := (map_ne_zero _).mpr hs'
  have hv2 : w.valuation E (IsLocalization.mk' E r s) ≠ 0 := (map_ne_zero _).mpr hx
  rw [← e3, WithZero.log_mul hv2 hv1] at e2
  linarith

theorem valuation_le_of_mem (w : HeightOneSpectrum (𝓞 E)) {𝔞 : FractionalIdeal (𝓞 E)⁰ E} {y : E} (hy : y ∈ 𝔞) :
    w.valuation E y ≤ WithZero.exp (-FractionalIdeal.count E w 𝔞) := by
  by_cases hy0 : y = 0
  · rw [hy0, map_zero]; exact zero_le'
  have hle : FractionalIdeal.spanSingleton (𝓞 E)⁰ y ≤ 𝔞 := (FractionalIdeal.spanSingleton_le_iff_mem).2 hy
  have hc := FractionalIdeal.count_mono E w ((FractionalIdeal.spanSingleton_ne_zero_iff).mpr hy0) hle
  rw [count_spanSingleton_eq w hy0] at hc
  have hv : w.valuation E y ≠ 0 := (map_ne_zero _).mpr hy0
  rw [← WithZero.exp_log hv, WithZero.exp_le_exp]
  linarith

theorem valAt_le_of_mem_locId (v : Pl F) (𝔞 : FractionalIdeal (𝓞 E)⁰ E) {w : HeightOneSpectrum (𝓞 E)}
    (h : w.under (𝓞 F) = v) {y : Fv F v ⊗[F] E} (hy : y ∈ GlobalTheory.SnMass.locId v 𝔞) :
    valAt v w y ≤ WithZero.exp (-FractionalIdeal.count E w 𝔞) := by
  rw [valAt_of_under h]
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨c, hc, x, hx, rfl⟩ := hy
    have h2 : Valued.v (algebraMap E (w.adicCompletion E) x) = w.valuation E x :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x
    rw [toCompl_tmul, map_mul, h2]
    have h1 : Valued.v (complMap h c) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (complMap_mem h hc)
    exact (mul_le_mul' h1 (valuation_le_of_mem w hx)).trans_eq (one_mul _)
  | zero => rw [map_zero, map_zero]; exact zero_le'
  | add y z _ _ hy hz => rw [map_add]; exact Valuation.map_add_le _ hy hz
  | neg y _ hy => rw [map_neg, Valuation.map_neg]; exact hy

theorem count_le_ordAt_of_mem_locId : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F) (𝔞 : FractionalIdeal (𝓞 E)⁰ E) (x : (Fv F v ⊗[F] E)ˣ), (x : Fv F v ⊗[F] E) ∈ GlobalTheory.SnMass.locId v 𝔞 → ∀ w ∈ Formalism.L2.Host.aboveF (L := E) F v, FractionalIdeal.count E w 𝔞 ≤ GlobalTheory.UnrTate.ordAt v w x := by
  intro F E _ _ _ _ _ v 𝔞 x hx w hw
  have h := valAt_le_of_mem_locId v 𝔞 (mem_aboveF.1 hw) hx
  rw [valAt_eq_exp, WithZero.exp_le_exp] at h
  linarith

end GlobalTheory.UnrTate
