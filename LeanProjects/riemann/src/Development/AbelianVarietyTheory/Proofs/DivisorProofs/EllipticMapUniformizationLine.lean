import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow

open NumberField IsDedekindDomain GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UnrEuler Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped nonZeroDivisors
open Formalism.L2.Host (aboveF)

namespace GlobalTheory.ConjCount

section General

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem count_coe_mult (v : HeightOneSpectrum R) {I : Ideal R} (hI : I ≠ ⊥) :
    FractionalIdeal.count K v (I : FractionalIdeal R⁰ K) = (multiplicity v.asIdeal I : ℤ) := by
  classical
  rw [FractionalIdeal.count_coe K v hI, Ideal.count_associates_factors_eq hI v.isPrime v.ne_bot,
    HeightOneSpectrum.count_normalizedFactors_eq_multiplicity hI v]

theorem count_map_ideal {f : R →+* R} (hf : Function.Bijective f) (w w' : HeightOneSpectrum R)
    (hw : w'.asIdeal.map f = w.asIdeal) {J : Ideal R} (hJ : J ≠ ⊥) :
    FractionalIdeal.count K w ((J.map f : Ideal R) : FractionalIdeal R⁰ K) =
      FractionalIdeal.count K w' (J : FractionalIdeal R⁰ K) := by
  have hJ' : J.map f ≠ ⊥ := fun h => hJ ((Ideal.map_eq_bot_iff_of_injective hf.1).1 h)
  rw [count_coe_mult w hJ', count_coe_mult w' hJ, ← hw]
  have hb : Function.Bijective (Ideal.mapHom f) := by
    constructor
    · intro A B h
      have h' : A.map f = B.map f := h
      rw [← Ideal.comap_map_of_bijective f hf (I := A), h', Ideal.comap_map_of_bijective f hf]
    · intro A
      exact ⟨A.comap f, Ideal.map_comap_of_surjective f hf.2 A⟩
  have := multiplicity_map_eq (RingEquiv.ofBijective (Ideal.mapHom f) hb) (a := w'.asIdeal) (b := J)
  exact congrArg _ this

theorem count_extended {f : R →+* R} (hf : Function.Bijective f) (hle : R⁰ ≤ Submonoid.comap f R⁰)
    (w w' : HeightOneSpectrum R) (hw : w'.asIdeal.map f = w.asIdeal) {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) :
    FractionalIdeal.count K w (I.extended K hle) = FractionalIdeal.count K w' I := by
  obtain ⟨a, J, ha, hIJ⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
  have ha' : algebraMap R K a ≠ 0 := by simpa using ha
  have hA : (Ideal.span {a} : Ideal R) ≠ ⊥ := by simpa using ha
  have h1 : ((Ideal.span {a} : Ideal R) : FractionalIdeal R⁰ K) * I = J := by
    rw [hIJ, FractionalIdeal.coeIdeal_span_singleton, ← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton,
      mul_inv_cancel₀ ha', FractionalIdeal.spanSingleton_one, one_mul]
  have hA0 : ((Ideal.span {a} : Ideal R) : FractionalIdeal R⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 hA
  have hJ : J ≠ ⊥ := by
    rw [← FractionalIdeal.coeIdeal_ne_zero (K := K), ← h1]
    exact mul_ne_zero hA0 hI
  have h2 := congrArg (FractionalIdeal.extended K hle) h1
  rw [FractionalIdeal.extended_mul, FractionalIdeal.extended_coeIdeal_eq_map,
    FractionalIdeal.extended_coeIdeal_eq_map] at h2
  have hA1 : (((Ideal.span {a} : Ideal R).map f : Ideal R) : FractionalIdeal R⁰ K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 fun h => hA ((Ideal.map_eq_bot_iff_of_injective hf.1).1 h)
  have hI1 : I.extended K hle ≠ 0 :=
    FractionalIdeal.extended_ne_zero K hle hf.1 hI zero_notMem_nonZeroDivisors
  have c1 := congrArg (FractionalIdeal.count K w') h1
  have c2 := congrArg (FractionalIdeal.count K w) h2
  rw [FractionalIdeal.count_mul K w' hA0 hI] at c1
  rw [FractionalIdeal.count_mul K w hA1 hI1, count_map_ideal hf w w' hw hA, count_map_ideal hf w w' hw hJ] at c2
  omega

end General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem conjO_bijective (σ : E →ₐ[F] E) : Function.Bijective (conjO σ) :=
  (RingOfIntegers.mapRingEquiv
    (AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)).toRingEquiv).bijective

theorem count_conjI : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (𝔠 : FractionalIdeal (𝓞 E)⁰ E), 𝔠 ≠ 0 → ∀ w : HeightOneSpectrum (𝓞 E), ∃ w' : HeightOneSpectrum (𝓞 E), w'.under (𝓞 F) = w.under (𝓞 F) ∧ FractionalIdeal.count E w (conjI σ 𝔠) = FractionalIdeal.count E w' 𝔠 := by
  intro F E _ _ _ _ _ σ 𝔠 h𝔠 w
  have hb := conjO_bijective σ
  have hm : (w.asIdeal.comap (conjO σ)).map (conjO σ) = w.asIdeal := Ideal.map_comap_of_surjective _ hb.2 _
  let w' : HeightOneSpectrum (𝓞 E) := ⟨w.asIdeal.comap (conjO σ), w.isPrime.comap _, fun h => w.ne_bot (by
    rw [← hm, h, Ideal.map_bot])⟩
  refine ⟨w', ?_, ?_⟩
  · apply HeightOneSpectrum.ext
    ext x
    have hx : conjO σ (algebraMap (𝓞 F) (𝓞 E) x) = algebraMap (𝓞 F) (𝓞 E) x := by
      apply RingOfIntegers.ext
      exact σ.commutes (x : F)
    change conjO σ (algebraMap (𝓞 F) (𝓞 E) x) ∈ w.asIdeal ↔ algebraMap (𝓞 F) (𝓞 E) x ∈ w.asIdeal
    rw [hx]
  · exact count_extended hb (conjO_le σ) w w' hm h𝔠

end GlobalTheory.ConjCount
