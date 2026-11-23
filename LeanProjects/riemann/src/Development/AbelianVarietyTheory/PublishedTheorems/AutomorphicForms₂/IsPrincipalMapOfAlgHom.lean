import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.NT GlobalTheory.Mem.Fld

namespace GlobalTheory.Published

def PrincipalIdealSt : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field L] [NumberField L] [Algebra K L],
    IsRayField K L ⊤ → ∀ 𝔞 : Ideal (𝓞 K), (𝔞.map (algebraMap (𝓞 K) (𝓞 L))).IsPrincipal

end GlobalTheory.Published

namespace GlobalTheory.HilbertClass

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]

omit [NumberField K] in

theorem isEmpty_realEmb : IsEmpty (K →+* ℝ) :=
  ⟨fun φ => IsTotallyComplex.complexEmbedding_not_isReal (Complex.ofRealHom.comp φ)
    (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => Complex.conj_ofReal _))⟩

theorem exists_rayPair_top_iff {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    (∃ α β : 𝓞 K, RayPair ⊤ α β ∧ I * Ideal.span {β} = Ideal.span {α}) ↔ I.IsPrincipal := by
  have hc : ∀ J : Ideal (𝓞 K), IsCoprime J ⊤ := fun J => by
    rw [← Ideal.one_eq_top]; exact isCoprime_one_right
  constructor
  · rintro ⟨α, β, ⟨-, hβ, -⟩, h⟩
    obtain ⟨c, rfl⟩ : β ∣ α := Ideal.span_singleton_le_span_singleton.1 (h ▸ Ideal.mul_le_right)
    rw [← Ideal.span_singleton_mul_span_singleton, mul_comm] at h
    exact ⟨c, mul_left_cancel₀ (by simpa using hβ) h⟩
  · rintro ⟨a, rfl⟩
    have := isEmpty_realEmb (K := K)
    exact ⟨a, 1, ⟨fun h => hI (by simp [h]), one_ne_zero, hc _, hc _, trivial, fun φ => isEmptyElim φ⟩, by simp⟩

theorem isRayField_top_iff (L : Type) [Field L] [NumberField L] [Algebra K L] : IsRayField K L ⊤ ↔
    IsAbelianGalois K L ∧ (∀ 𝔭 : HeightOneSpectrum (𝓞 K), UnramIn L 𝔭) ∧
      Subgroup.closure {σ : L ≃ₐ[K] L | ∃ 𝔭 : HeightOneSpectrum (𝓞 K), IsFrob L 𝔭 σ} = ⊤ ∧
      ∀ I : Ideal (𝓞 K), I ≠ ⊥ → ((∀ χ : (L ≃ₐ[K] L) →* ℂˣ, heckeIdeal L χ I = 1) ↔ I.IsPrincipal) := by
  have hc : ∀ J : Ideal (𝓞 K), IsCoprime J ⊤ := fun J => by
    rw [← Ideal.one_eq_top]; exact isCoprime_one_right
  have hp : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ ⊤ := fun 𝔭 h =>
    𝔭.isPrime.ne_top (top_le_iff.1 (Ideal.le_of_dvd h))
  simp only [IsRayField, hp, hc, not_false_eq_true, forall_const, true_and]
  refine and_congr_right' (and_congr_right' (and_congr_right' (forall₂_congr fun I hI => ?_)))
  rw [exists_rayPair_top_iff hI]

theorem isRayField_self_top_iff : IsRayField K K ⊤ ↔ IsPrincipalIdealRing (𝓞 K) := by
  have h1 : ∀ (I : Ideal (𝓞 K)) (χ : (K ≃ₐ[K] K) →* ℂˣ), heckeIdeal K χ I = 1 := fun I χ => by
    rw [Subsingleton.elim χ 1]
    simp [heckeIdeal, heckeVal_one]
  rw [isRayField_top_iff]
  refine ⟨fun h => ⟨fun I => ?_⟩, fun h => ⟨inferInstance, fun _ σ _ => Subsingleton.elim _ _, Subsingleton.elim _ _,
    fun I _ => iff_of_true (h1 I) (h.principal I)⟩⟩
  by_cases hI : I = ⊥
  · rw [hI]; infer_instance
  · exact (h.2.2.2 I hI).1 (h1 I)

example : IsTotallyComplex (CyclotomicField 3 ℚ) ∧ IsRayField (CyclotomicField 3 ℚ) (CyclotomicField 3 ℚ) ⊤ :=
  have := IsCyclotomicExtension.Rat.isTotallyComplex (n := 3) (CyclotomicField 3 ℚ) (by norm_num)
  ⟨this, isRayField_self_top_iff.2 (IsCyclotomicExtension.Rat.three_pid _)⟩

omit [NumberField K] [IsTotallyComplex K] in

theorem isPrincipal_map_of_algHom {L M : Type} [Field L] [Algebra K L] [Field M] [Algebra K M] (f : L →ₐ[K] M)
    {𝔞 : Ideal (𝓞 K)} (h : (𝔞.map (algebraMap (𝓞 K) (𝓞 L))).IsPrincipal) :
    (𝔞.map (algebraMap (𝓞 K) (𝓞 M))).IsPrincipal := by
  have e : algebraMap (𝓞 K) (𝓞 M) = (RingOfIntegers.mapRingHom f.toRingHom).comp (algebraMap (𝓞 K) (𝓞 L)) :=
    RingHom.ext fun x => RingOfIntegers.ext (f.commutes x).symm
  obtain ⟨a, ha⟩ := h
  rw [e, ← Ideal.map_map, ha]
  exact ⟨_, by rw [Ideal.submodule_span_eq, Ideal.map_span, Set.image_singleton, Ideal.submodule_span_eq]⟩

end GlobalTheory.HilbertClass

namespace GlobalTheory.Published

open GlobalTheory.HilbertClass

variable {K L M : Type} [Field K] [NumberField K] [IsTotallyComplex K] [Field L] [NumberField L] [Algebra K L]
  [Field M] [Algebra K M]

theorem PrincipalIdealSt.of_algHom (H : PrincipalIdealSt) (h : IsRayField K L ⊤) (f : L →ₐ[K] M)
    (𝔞 : Ideal (𝓞 K)) : (𝔞.map (algebraMap (𝓞 K) (𝓞 M))).IsPrincipal :=
  isPrincipal_map_of_algHom f (H K L h 𝔞)

theorem PrincipalIdealSt.of_isRayField (H : PrincipalIdealSt) (hR : RayField) {𝔮 : Ideal (𝓞 K)} (h𝔮 : 𝔮 ≠ ⊥)
    (h : IsRayField K L 𝔮) (f : L →ₐ[K] M) (𝔞 : Ideal (𝓞 K)) :
    (𝔞.map (algebraMap (𝓞 K) (𝓞 M))).IsPrincipal := by
  obtain ⟨L₀, _, _, _, h₀⟩ := rayField_iff.1 hR K ⊤ top_ne_bot
  have := h.1
  have := h₀.1
  obtain ⟨g⟩ := nonempty_algHom_of_isRay_of_dvd (L := L) (L' := L₀) h𝔮 (Ideal.dvd_iff_le.2 le_top) h.2 h₀.2
  exact H.of_algHom h₀ (f.comp g) 𝔞

theorem PrincipalIdealSt.of_isRayFieldIn (H : PrincipalIdealSt) (hR : RayField) {E : Type} [Field E] [NumberField E]
    [IsTotallyComplex E] {φ : E →+* ℂ} {𝔮 : Ideal (𝓞 E)} (h𝔮 : 𝔮 ≠ ⊥) {R N : IntermediateField ℚ ℂ}
    (h : IsRayFieldIn φ 𝔮 R) (hle : R ≤ N) (𝔞 : Ideal (𝓞 E)) :
    (𝔞.map (RingOfIntegers.mapRingHom (φ.codRestrict N fun x => hle (h.emb_mem x)))).IsPrincipal := by
  have := h.numberField
  let := algOf φ R h.emb_mem
  let := algOf φ N fun x => hle (h.emb_mem x)
  exact H.of_isRayField hR h𝔮 h.isRayField
    { (IntermediateField.inclusion hle).toRingHom with commutes' := fun _ => rfl } 𝔞

end GlobalTheory.Published

end
