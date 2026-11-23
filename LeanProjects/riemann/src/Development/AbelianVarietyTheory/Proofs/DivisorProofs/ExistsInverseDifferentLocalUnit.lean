import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemInverseDifferentIdealPowRealIffUnramifiedCm
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.ImagDifferent

theorem exists_local_generator {R : Type} [CommRing R] [IsDedekindDomain R] (I : Ideal R)
    (hI : I ≠ ⊥) (v : HeightOneSpectrum R) :
    ∃ f ∈ I, f ≠ 0 ∧ ∃ s ∉ v.asIdeal, ∀ d ∈ I, ∃ c : R, s * d = f * c := by
  have hlt : ¬ I ≤ I * v.asIdeal := by
    intro h
    have h1 : I * v.asIdeal = I * ⊤ := by
      rw [Ideal.mul_top]; exact le_antisymm Ideal.mul_le_left h
    exact v.isPrime.ne_top (mul_left_cancel₀ hI h1)
  obtain ⟨f, hf, hf'⟩ := SetLike.not_le_iff_exists.1 hlt
  have hdvd : I ∣ Ideal.span {f} := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hf)
  obtain ⟨J, hJ⟩ := hdvd
  have hJv : ¬ J ≤ v.asIdeal := by
    intro h
    apply hf'
    have : f ∈ I * J := hJ ▸ Ideal.mem_span_singleton_self f
    exact Ideal.mul_mono_right h this
  obtain ⟨s, hs, hs'⟩ := SetLike.not_le_iff_exists.1 hJv
  refine ⟨f, hf, fun h => hf' (h ▸ zero_mem _), s, hs', fun d hd => ?_⟩
  have : d * s ∈ Ideal.span {f} := hJ ▸ Ideal.mul_mem_mul hd hs
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 this
  exact ⟨c, by rw [mul_comm, hc]⟩

theorem exists_sub_notMem {A B : Type} [CommRing A] [CommRing B] [IsDomain B] [Algebra A B]
    [Algebra.Unramified A B] (g : B →ₐ[A] B) (hg : ∃ x, g x ≠ x) (w : Ideal B) (hw : w ≠ ⊤) :
    ∃ x, x - g x ∉ w := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨t, ht, ht1⟩ := (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := A) (S := B)).1
    inferInstance
  let φ : B ⊗[A] B →ₐ[A] B := Algebra.TensorProduct.lift (AlgHom.id A B) g (fun _ _ => Commute.all _ _)
  obtain ⟨x, hx⟩ := hg
  have h0 : φ t = 0 := by
    have := congrArg φ (ht x)
    rw [map_mul, map_zero, map_sub] at this
    simp only [φ, Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, map_one, one_mul, mul_one] at this
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hx
    · exact h
  have hall : ∀ u : B ⊗[A] B, Algebra.TensorProduct.lmul' A u - φ u ∈ w := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      simp only [φ, Algebra.TensorProduct.lift_tmul, AlgHom.id_apply,
        Algebra.TensorProduct.lmul'_apply_tmul]
      rw [← mul_sub]
      exact w.mul_mem_left _ (hcon b)
    | add a b ha hb =>
      rw [map_add, map_add, add_sub_add_comm]
      exact w.add_mem ha hb
  have := hall t
  rw [ht1, h0, sub_zero] at this
  exact hw ((Ideal.eq_top_iff_one w).2 this)

theorem forall_trace_iff {E : Type} [Field E] [NumberField E] (t : E) :
    (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * t))) ↔
      ∀ d ∈ differentIdeal ℤ (𝓞 E), IsIntegral ℤ ((d : E) * t) := by
  have hd : (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E)) =
      ((differentIdeal ℤ (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E))⁻¹ := by
    rw [coeIdeal_differentIdeal ℤ ℚ, inv_inv]
  have h1 : (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * t))) ↔
      t ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [FractionalIdeal.mem_dual (one_ne_zero' (FractionalIdeal (𝓞 E)⁰ E))]
    constructor
    · intro h a ha
      obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
      rw [Algebra.traceForm_apply, mul_comm]
      exact IsIntegrallyClosed.isIntegral_iff.1 (h o)
    · intro h o
      have := h o ((FractionalIdeal.mem_one_iff _).2 ⟨o, rfl⟩)
      rw [Algebra.traceForm_apply, mul_comm] at this
      exact IsIntegrallyClosed.isIntegral_iff.2 this
  rw [h1, hd, FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.2 differentIdeal_ne_bot)]
  constructor
  · intro h d hd
    obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1
      (h _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨d, hd, rfl⟩))
    have hc' : (d : E) * t = (c : E) := by rw [mul_comm]; exact hc.symm
    rw [hc']
    exact c.2
  · intro h z hz
    obtain ⟨d, hd, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hz
    exact (FractionalIdeal.mem_one_iff _).2 ⟨⟨_, h d hd⟩, mul_comm _ _⟩

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_imag_unit (σ : E →ₐ[F] E) (h : IsCMExt F E σ) [Algebra.Unramified (𝓞 F) (𝓞 E)]
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ y : 𝓞 E, σ (y : E) = -(y : E) ∧ ∃ s ∉ v.asIdeal, algebraMap (𝓞 F) (𝓞 E) s = y * y := by
  have hσσ : ∀ x, σ (σ x) = x := by
    intro x
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [h.2.2.2, h.2.2.2, star_star]
  let g : 𝓞 E →ₐ[𝓞 F] 𝓞 E :=
    { RingOfIntegers.mapRingHom (σ : E →+* E) with
      commutes' := fun r => by
        apply RingOfIntegers.ext
        exact σ.commutes (r : F) }
  have hgc : ∀ x : 𝓞 E, ((g x : 𝓞 E) : E) = σ x := fun x => rfl
  have hg : ∃ x, g x ≠ x := by
    by_contra hcon
    push_neg at hcon
    apply GlobalTheory.SnMass.SkewVol.cm_sigma_ne_id h
    ext z
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) z
    have ha := hgc a
    have hb := hgc b
    rw [hcon] at ha hb
    rw [map_div₀, AlgHom.id_apply]
    exact congrArg₂ (· / ·) ha.symm hb.symm
  haveI := v.isMaximal
  obtain ⟨w, hw, hwv⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E) v.asIdeal
    (by rw [(RingHom.injective_iff_ker_eq_bot _).1 (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))]; exact bot_le)
  obtain ⟨x, hx⟩ := exists_sub_notMem g hg w hw.ne_top
  have hy : σ ((x - g x : 𝓞 E) : E) = -((x - g x : 𝓞 E) : E) := by
    have : ((x - g x : 𝓞 E) : E) = (x : E) - σ x := by rw [← hgc]; rfl
    rw [this, map_sub, hσσ]; ring
  set y := x - g x
  refine ⟨y, hy, ?_⟩
  obtain ⟨n, hn⟩ := GlobalTheory.SnMass.SkewVol.mem_range_of_cm_fixed h (x := (y : E) * y)
    (by rw [map_mul, hy]; ring)
  have hint : IsIntegral ℤ n := by
    rw [← isIntegral_algHom_iff ((algebraMap F E).toIntAlgHom) (algebraMap F E).injective]
    show IsIntegral ℤ (algebraMap F E n)
    rw [hn]
    exact y.2.mul y.2
  have he : algebraMap (𝓞 F) (𝓞 E) ⟨n, hint⟩ = y * y := by
    apply RingOfIntegers.ext
    exact hn
  refine ⟨⟨n, hint⟩, fun hs => ?_, he⟩
  rw [← hwv] at hs
  have hs' : y * y ∈ w := he ▸ Ideal.mem_comap.1 hs
  exact (hw.isPrime.mem_or_mem hs').elim hx hx

theorem exists_imag_generator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ v : HeightOneSpectrum (𝓞 F), ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ ∧
    ∃ s : 𝓞 F, s ∉ v.asIdeal ∧
    (∀ t : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * t))) → IsIntegral ℤ (δ * t)) ∧
    (∀ t : E, IsIntegral ℤ (δ * t) → ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * (algebraMap F E (s : F) * t)))) := by
  intro F E _ _ _ _ _ σ h hu v
  obtain ⟨y, hy, s₁, hs₁, hyy⟩ := exists_imag_unit σ h v
  obtain ⟨f, hf, hf0, s₂, hs₂, hloc⟩ :=
    exists_local_generator (differentIdeal ℤ (𝓞 F)) differentIdeal_ne_bot v
  have hdiff := GlobalTheory.SnMass.SkewVol.differentIdeal_eq_map_of_unramified (F := F) (E := E) inferInstance
  have key : ∀ a : 𝓞 F, ((algebraMap (𝓞 F) (𝓞 E) a : 𝓞 E) : E) = algebraMap F E (a : F) :=
    fun a => rfl
  have hy0 : y ≠ 0 := by
    rintro rfl
    apply hs₁
    have : s₁ = 0 := FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E) (by rw [hyy]; simp)
    rw [this]; exact zero_mem _
  refine ⟨algebraMap F E (f : F) * y, ?_, ?_, s₁ * s₂, ?_, ?_, ?_⟩
  · refine mul_ne_zero ?_ ?_
    · simpa using hf0
    · simpa using hy0
  · rw [map_mul, AlgHom.commutes, hy]; ring
  · exact fun hm => (v.isPrime.mem_or_mem hm).elim hs₁ hs₂
  · intro t ht
    have := (forall_trace_iff t).1 ht (algebraMap (𝓞 F) (𝓞 E) f * y)
      (by rw [hdiff]; exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hf))
    exact this
  · intro t ht
    rw [forall_trace_iff, hdiff]
    intro d hd
    have hd' : ∃ c : 𝓞 E, algebraMap (𝓞 F) (𝓞 E) s₂ * d = algebraMap (𝓞 F) (𝓞 E) f * c := by
      have hle : (differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E)) ≤
          (Ideal.span {algebraMap (𝓞 F) (𝓞 E) f}).colon {algebraMap (𝓞 F) (𝓞 E) s₂} := by
        rw [Ideal.map_le_iff_le_comap]
        intro a ha
        obtain ⟨c, hc⟩ := hloc a ha
        rw [Ideal.mem_comap, Submodule.mem_colon_singleton, smul_eq_mul, ← map_mul, mul_comm, hc,
          map_mul]
        exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
      have := hle hd
      rw [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm] at this
      exact Ideal.mem_span_singleton.1 this
    obtain ⟨c, hc⟩ := hd'
    have hc' : algebraMap F E (s₂ : F) * (d : E) = algebraMap F E (f : F) * c :=
      congrArg (fun z : 𝓞 E => (z : E)) hc
    have hyy' : algebraMap F E (s₁ : F) = (y : E) * y :=
      congrArg (fun z : 𝓞 E => (z : E)) hyy
    have e : (d : E) * (algebraMap F E ((s₁ * s₂ : 𝓞 F) : F) * t) =
        ((y : E) * c) * (algebraMap F E (f : F) * y * t) := by
      have : ((s₁ * s₂ : 𝓞 F) : F) = (s₁ : F) * s₂ := rfl
      rw [this, map_mul, hyy']
      linear_combination ((y : E) * y * t) * hc'
    rw [e]
    exact (y.2.mul c.2).mul ht

end GlobalTheory.ImagDifferent
