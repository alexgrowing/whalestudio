import Mathlib
import GroundTheory.GlobalFields.TateThesis.SchwartzBruhat
import GroundTheory.GlobalFields.TateThesis.TraceLatticePoisson
import GroundTheory.GlobalFields.IdeleGroups.ClassGroup

namespace GroundTheory.Global

open NumberField NumberField.mixedEmbedding IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  MeasureTheory Measure Filter WithZero
open scoped NumberField.AdeleRing ENNReal NNReal SchwartzMap FourierTransform Real Classical
  nonZeroDivisors

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem valuation_le_of_mem_fractionalIdeal (v : HeightOneSpectrum (𝓞 K))
    {J : FractionalIdeal (𝓞 K)⁰ K} {y : K} (hy : y ∈ J) :
    v.valuation K y ≤ exp (-FractionalIdeal.count K v J) := by
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [map_zero]; exact zero_le
  have hle : FractionalIdeal.spanSingleton (𝓞 K)⁰ y ≤ J :=
    FractionalIdeal.spanSingleton_le_iff_mem.mpr hy
  have hc := FractionalIdeal.count_mono K v
    ((FractionalIdeal.spanSingleton_ne_zero_iff).mpr hy0) hle
  rw [count_spanSingleton v hy0] at hc
  have hv0 : v.valuation K y ≠ 0 := by rwa [Ne, map_eq_zero]
  rw [← exp_log hv0, exp_le_exp]
  omega

theorem mem_fractionalIdeal_iff_forall_valuation_le (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (k : K) :
    k ∈ (I : FractionalIdeal (𝓞 K)⁰ K) ↔ ∀ v : HeightOneSpectrum (𝓞 K),
      v.valuation K k ≤ exp (-FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K)) := by
  refine ⟨fun hk v ↦ valuation_le_of_mem_fractionalIdeal v hk, fun hk ↦ ?_⟩
  rw [← inv_inv (I : FractionalIdeal (𝓞 K)⁰ K),
    FractionalIdeal.mem_inv_iff (inv_ne_zero I.ne_zero)]
  intro y hy
  have hint : ∀ v : HeightOneSpectrum (𝓞 K), v.valuation K (k * y) ≤ 1 := by
    intro v
    have h2 := valuation_le_of_mem_fractionalIdeal v hy
    rw [FractionalIdeal.count_inv] at h2
    rw [map_mul]
    calc v.valuation K k * v.valuation K y
        ≤ exp (-FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K)) *
          exp (- -FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K)) :=
          mul_le_mul' (hk v) h2
      _ = 1 := by rw [← exp_add, neg_neg, neg_add_cancel, exp_zero]
  obtain ⟨r, hr⟩ := mem_integers_of_valuation_le_one (R := 𝓞 K) K (k * y) hint
  exact (FractionalIdeal.mem_one_iff _).mpr ⟨r, hr⟩

theorem algebraMap_mem_idealFiniteAdeles_iff (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (k : K) :
    algebraMap K 𝔸ᶠ[K] k ∈ idealFiniteAdeles I ↔ k ∈ (I : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [mem_idealFiniteAdeles, mem_fractionalIdeal_iff_forall_valuation_le]
  refine forall_congr' fun v ↦ ?_
  change Valued.v (k : v.adicCompletion K) ≤ _ ↔ _
  rw [valuedAdicCompletion_eq_valuation']

theorem exists_sub_mem_idealFiniteAdeles (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (b : 𝔸ᶠ[K]) :
    ∃ ξ : K, b - algebraMap K 𝔸ᶠ[K] ξ ∈ idealFiniteAdeles I := by
  obtain ⟨d, hdI, hd0⟩ : ∃ d ∈ (I : FractionalIdeal (𝓞 K)⁰ K), d ≠ 0 := by
    have hne : ((I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) ≠ ⊥ := by
      rw [Ne, FractionalIdeal.coeToSubmodule_eq_bot]
      exact I.ne_zero
    exact Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨k, hk⟩ := exists_sub_mem_integralFiniteAdeles (R := 𝓞 K) (algebraMap K 𝔸ᶠ[K] d⁻¹ * b)
  refine ⟨d * k, fun v ↦ ?_⟩
  have hb : b - algebraMap K 𝔸ᶠ[K] (d * k) = algebraMap K 𝔸ᶠ[K] d *
      (algebraMap K 𝔸ᶠ[K] d⁻¹ * b - algebraMap K 𝔸ᶠ[K] k) := by
    rw [mul_sub, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hd0, map_one, one_mul, map_mul]
  have hdv := (mem_fractionalIdeal_iff_forall_valuation_le I d).mp hdI v
  have hkv : Valued.v ((algebraMap K 𝔸ᶠ[K] d⁻¹ * b - algebraMap K 𝔸ᶠ[K] k) v) ≤ 1 := hk v
  rw [hb]
  change Valued.v ((d : v.adicCompletion K) * _) ≤ _
  rw [Valuation.map_mul, valuedAdicCompletion_eq_valuation']
  calc v.valuation K d * Valued.v ((algebraMap K 𝔸ᶠ[K] d⁻¹ * b - algebraMap K 𝔸ᶠ[K] k) v)
      ≤ exp (-FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K)) * 1 := mul_le_mul' hdv hkv
    _ = _ := mul_one _

theorem finiteAdelicChar_algebraMap_mul (ξ η : K) :
    (finiteAdelicChar K (algebraMap K 𝔸ᶠ[K] ξ * algebraMap K 𝔸ᶠ[K] η) : ℂ) =
      𝐞 (mixedTraceForm K (mixedEmbedding K ξ) (mixedEmbedding K η)) := by
  have h := adelicChar_mul_eq (algebraMap K 𝔸[K] ξ) (algebraMap K 𝔸[K] η)
  rw [← map_mul, adelicChar_algebraMap] at h
  simp only [adeleRing_algebraMap_fst, adeleRing_algebraMap_snd,
    homeomorphMixedSpace_algebraMap] at h
  set t := mixedTraceForm K (mixedEmbedding K ξ) (mixedEmbedding K η)
  have he : (𝐞 t : ℂ) * 𝐞 (-t) = 1 := by
    rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one,
      Circle.coe_one]
  calc (finiteAdelicChar K (algebraMap K 𝔸ᶠ[K] ξ * algebraMap K 𝔸ᶠ[K] η) : ℂ)
      = 𝐞 t * 𝐞 (-t) * finiteAdelicChar K (algebraMap K 𝔸ᶠ[K] ξ * algebraMap K 𝔸ᶠ[K] η) := by
        rw [he, one_mul]
    _ = 𝐞 t := by rw [mul_assoc, ← h, Circle.coe_one, mul_one]

def idealLatticeEquiv (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ((J : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) ≃ idealLattice K J :=
  (LinearEquiv.ofInjective _ (fun _ _ h ↦ Subtype.ext (mixedEmbedding_injective K h))).toEquiv

theorem coe_idealLatticeEquiv (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (y : ((J : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) :
    ((idealLatticeEquiv J y : idealLattice K J) : mixedSpace K) = mixedEmbedding K (y : K) :=
  rfl

theorem summable_norm_iff_and_tsum_eq_of_coset (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (c : K)
    (g : mixedSpace K → ℂ) (f : K → ℂ)
    (hf : ∀ ξ, f ξ = if ξ - c ∈ (J : FractionalIdeal (𝓞 K)⁰ K) then g (mixedEmbedding K ξ) else 0) :
    (Summable (fun ξ ↦ ‖f ξ‖) ↔
      Summable (fun α : idealLattice K J ↦ ‖g (α + mixedEmbedding K c)‖)) ∧
      ∑' ξ, f ξ = ∑' α : idealLattice K J, g (α + mixedEmbedding K c) := by
  set e := idealLatticeEquiv J
  let h : idealLattice K J → K := fun α ↦ c + ((e.symm α : _) : K)
  have hinj : Function.Injective h := fun α β hαβ ↦
    e.symm.injective (Subtype.ext (add_left_cancel hαβ))
  have hsupp : ∀ ξ ∉ Set.range h, f ξ = 0 := by
    intro ξ hξ
    rw [hf, if_neg]
    intro hm
    refine hξ ⟨e ⟨ξ - c, hm⟩, ?_⟩
    simp only [h, Equiv.symm_apply_apply]
    abel
  have hfh : ∀ α, f (h α) = g (α + mixedEmbedding K c) := by
    intro α
    have hm : h α - c ∈ (J : FractionalIdeal (𝓞 K)⁰ K) := by
      simp only [h, add_sub_cancel_left]
      exact (e.symm α).2
    rw [hf, if_pos hm]
    congr 1
    have he := coe_idealLatticeEquiv J (e.symm α)
    rw [Equiv.apply_symm_apply] at he
    simp only [h, map_add]
    rw [← he, add_comm]
  refine ⟨?_, ?_⟩
  · rw [← hinj.summable_iff (f := fun ξ ↦ ‖f ξ‖) (fun ξ hξ ↦ by simp [hsupp ξ hξ])]
    simp only [Function.comp_def, hfh]
  · rw [← hinj.tsum_eq (fun ξ hξ ↦ by_contra fun hn ↦ hξ (hsupp ξ hn))]
    simp only [hfh]

theorem schwartzBruhatTensor_algebraMap (φ : 𝓢(mixedSpace K, ℂ)) (g : 𝔸ᶠ[K] → ℂ) (ξ : K) :
    schwartzBruhatTensor φ g (algebraMap K 𝔸[K] ξ) =
      φ (mixedEmbedding K ξ) * g (algebraMap K 𝔸ᶠ[K] ξ) := by
  simp only [schwartzBruhatTensor, adeleRing_algebraMap_fst, adeleRing_algebraMap_snd,
    homeomorphMixedSpace_algebraMap]

theorem algebraMap_sub_mem_idealFiniteAdeles_iff {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {b : 𝔸ᶠ[K]}
    {ξ₀ : K} (hξ₀ : b - algebraMap K 𝔸ᶠ[K] ξ₀ ∈ idealFiniteAdeles I) (ξ : K) :
    algebraMap K 𝔸ᶠ[K] ξ - b ∈ idealFiniteAdeles I ↔ ξ - ξ₀ ∈ (I : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [← algebraMap_mem_idealFiniteAdeles_iff, map_sub]
  have : algebraMap K 𝔸ᶠ[K] ξ - algebraMap K 𝔸ᶠ[K] ξ₀ =
      (algebraMap K 𝔸ᶠ[K] ξ - b) + (b - algebraMap K 𝔸ᶠ[K] ξ₀) := by abel
  rw [this, AddSubgroup.add_mem_cancel_right _ hξ₀]

theorem poisson_schwartzBruhatTensor_cosetIndicator (φ : 𝓢(mixedSpace K, ℂ))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (b : 𝔸ᶠ[K]) :
    Summable (fun ξ : K ↦ ‖schwartzBruhatTensor φ (cosetIndicator I b) (algebraMap K 𝔸[K] ξ)‖) ∧
      Summable (fun ξ : K ↦
        ‖adelicFourier K (schwartzBruhatTensor φ (cosetIndicator I b)) (algebraMap K 𝔸[K] ξ)‖) ∧
      ∑' ξ : K, schwartzBruhatTensor φ (cosetIndicator I b) (algebraMap K 𝔸[K] ξ) =
        ∑' ξ : K,
          adelicFourier K (schwartzBruhatTensor φ (cosetIndicator I b)) (algebraMap K 𝔸[K] ξ) := by
  obtain ⟨ξ₀, hξ₀⟩ := exists_sub_mem_idealFiniteAdeles I b
  set a := mixedEmbedding K ξ₀
  set μ : ℂ := ((finiteAdeleMeasure K (idealFiniteAdeles I)).toReal : ℂ)

  have hL := summable_norm_iff_and_tsum_eq_of_coset I ξ₀ φ
    (fun ξ ↦ schwartzBruhatTensor φ (cosetIndicator I b) (algebraMap K 𝔸[K] ξ)) fun ξ ↦ by
      rw [schwartzBruhatTensor_algebraMap, cosetIndicator_apply]
      by_cases hξ : ξ - ξ₀ ∈ (I : FractionalIdeal (𝓞 K)⁰ K)
      · rw [if_pos ((algebraMap_sub_mem_idealFiniteAdeles_iff hξ₀ ξ).mpr hξ), if_pos hξ, mul_one]
      · rw [if_neg (fun h ↦ hξ ((algebraMap_sub_mem_idealFiniteAdeles_iff hξ₀ ξ).mp h)),
          if_neg hξ, mul_zero]

  have hR := summable_norm_iff_and_tsum_eq_of_coset (traceDualIdeal K I) 0
    (fun x ↦ μ * (mixedFourier K φ x * 𝐞 (mixedTraceForm K x a)))
    (fun η ↦ adelicFourier K (schwartzBruhatTensor φ (cosetIndicator I b)) (algebraMap K 𝔸[K] η))
    fun η ↦ by
      rw [adelicFourier_schwartzBruhatTensor, schwartzBruhatTensor_algebraMap,
        finiteFourier_cosetIndicator, mixedFourierSchwartz_apply, sub_zero]
      by_cases hη : η ∈ (traceDualIdeal K I : FractionalIdeal (𝓞 K)⁰ K)
      · have hη' : algebraMap K 𝔸ᶠ[K] η ∈ idealFiniteAdeles (traceDualIdeal K I) :=
          (algebraMap_mem_idealFiniteAdeles_iff _ η).mpr hη
        rw [if_pos hη, Set.indicator_of_mem (SetLike.mem_coe.mpr hη'), Pi.one_apply, mul_one]
        have hb : b * algebraMap K 𝔸ᶠ[K] η = algebraMap K 𝔸ᶠ[K] ξ₀ * algebraMap K 𝔸ᶠ[K] η +
            (b - algebraMap K 𝔸ᶠ[K] ξ₀) * algebraMap K 𝔸ᶠ[K] η := by ring
        rw [hb, AddChar.map_add_eq_mul,
          (forall_finiteAdelicChar_mul_eq_one_iff I _).mpr hη' _ hξ₀, mul_one,
          finiteAdelicChar_algebraMap_mul, mixedTraceForm_comm K a]
        ring
      · have hη' : algebraMap K 𝔸ᶠ[K] η ∉ idealFiniteAdeles (traceDualIdeal K I) :=
          fun h ↦ hη ((algebraMap_mem_idealFiniteAdeles_iff _ η).mp h)
        rw [if_neg hη, Set.indicator_of_notMem (by simpa using hη'), mul_zero, mul_zero, mul_zero]
  simp only [map_zero, add_zero] at hR
  refine ⟨hL.1.mpr (idealLattice_summable_norm K I φ a), hR.1.mpr ?_, ?_⟩
  · simpa only [norm_mul] using (traceDualIdeal_summable_norm K I φ a).mul_left ‖μ‖
  · rw [hL.2, hR.2, idealLattice_poisson_summation, tsum_mul_left, Complex.real_smul]
    congr 1
    simp only [μ, finiteAdeleMeasure_idealFiniteAdeles_toReal, mul_inv]
    push_cast
    rw [Int.norm_eq_abs]

theorem schwartzBruhatTensor_sum (φ : 𝓢(mixedSpace K, ℂ)) {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (g : ι → 𝔸ᶠ[K] → ℂ) :
    schwartzBruhatTensor φ (∑ i ∈ s, c i • g i) = ∑ i ∈ s, c i • schwartzBruhatTensor φ (g i) := by
  funext x
  simp only [schwartzBruhatTensor, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

theorem schwartzBruhat_le_span_cosetIndicator :
    schwartzBruhat K ≤ Submodule.span ℂ {F | ∃ (φ : 𝓢(mixedSpace K, ℂ))
      (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (b : 𝔸ᶠ[K]), F = schwartzBruhatTensor φ (cosetIndicator I b)} := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨φ, g, hg, rfl⟩
  obtain ⟨I, s, hs⟩ := exists_eq_sum_cosetIndicator hg
  rw [hs, schwartzBruhatTensor_sum]
  exact Submodule.sum_mem _ fun b _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨φ, I, b, rfl⟩)

theorem poisson_of_mem_span {F : 𝔸[K] → ℂ} (hF : F ∈ Submodule.span ℂ {F | ∃ (φ : 𝓢(mixedSpace K, ℂ))
      (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (b : 𝔸ᶠ[K]), F = schwartzBruhatTensor φ (cosetIndicator I b)}) :
    Summable (fun ξ : K ↦ ‖F (algebraMap K 𝔸[K] ξ)‖) ∧
      Summable (fun ξ : K ↦ ‖adelicFourier K F (algebraMap K 𝔸[K] ξ)‖) ∧
      ∑' ξ : K, F (algebraMap K 𝔸[K] ξ) = ∑' ξ : K, adelicFourier K F (algebraMap K 𝔸[K] ξ) := by
  have hsub : Submodule.span ℂ {F | ∃ (φ : 𝓢(mixedSpace K, ℂ))
      (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (b : 𝔸ᶠ[K]), F = schwartzBruhatTensor φ (cosetIndicator I b)} ≤
      schwartzBruhat K := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨φ, I, b, rfl⟩
    exact schwartzBruhatTensor_mem φ (cosetIndicator_mem_finiteSchwartzBruhat I b)
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, I, b, rfl⟩ := hG
    exact poisson_schwartzBruhatTensor_cosetIndicator φ I b
  | zero => simp [adelicFourier_zero]
  | add G H hG hH ihG ihH =>
    rw [adelicFourier_add (integrable_of_mem_schwartzBruhat (hsub hG))
      (integrable_of_mem_schwartzBruhat (hsub hH))]
    refine ⟨(ihG.1.add ihH.1).of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun ξ ↦ norm_add_le _ _,
      (ihG.2.1.add ihH.2.1).of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun ξ ↦ norm_add_le _ _, ?_⟩
    simp only [Pi.add_apply]
    rw [ihG.1.of_norm.tsum_add ihH.1.of_norm, ihG.2.1.of_norm.tsum_add ihH.2.1.of_norm, ihG.2.2,
      ihH.2.2]
  | smul c G hG ih =>
    rw [adelicFourier_smul]
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
    exact ⟨ih.1.mul_left _, ih.2.1.mul_left _, by rw [tsum_mul_left, tsum_mul_left, ih.2.2]⟩

theorem summable_norm_algebraMap_of_mem_schwartzBruhat {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K) :
    Summable fun ξ : K ↦ ‖F (algebraMap K 𝔸[K] ξ)‖ :=
  (poisson_of_mem_span (schwartzBruhat_le_span_cosetIndicator hF)).1

theorem tsum_algebraMap_eq_tsum_adelicFourier {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K) :
    ∑' ξ : K, F (algebraMap K 𝔸[K] ξ) = ∑' ξ : K, adelicFourier K F (algebraMap K 𝔸[K] ξ) :=
  (poisson_of_mem_span (schwartzBruhat_le_span_cosetIndicator hF)).2.2

def mixedMulLeft (u : (mixedSpace K)ˣ) : mixedSpace K ≃L[ℝ] mixedSpace K :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x ↦ (u : mixedSpace K) * x
      invFun := fun x ↦ ((u⁻¹ : (mixedSpace K)ˣ) : mixedSpace K) * x
      map_add' := mul_add _
      map_smul' := fun r x ↦ mul_smul_comm r _ x
      left_inv := fun x ↦ Units.inv_mul_cancel_left u x
      right_inv := fun x ↦ Units.mul_inv_cancel_left u x }

theorem mixedMulLeft_apply (u : (mixedSpace K)ˣ) (x : mixedSpace K) :
    mixedMulLeft u x = (u : mixedSpace K) * x :=
  rfl

theorem comp_smul_mem_schwartzBruhat (a : IdeleGroup K) {F : 𝔸[K] → ℂ}
    (hF : F ∈ schwartzBruhat K) : (fun x ↦ F (a • x)) ∈ schwartzBruhat K := by
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    set u : (mixedSpace K)ˣ := Units.map
      (InfiniteAdeleRing.ringEquiv_mixedSpace K).toRingHom.toMonoidHom (IdeleGroup.toInfinite K a)
    set c : (𝔸ᶠ[K])ˣ := IdeleGroup.toFinite K a
    have hg' : (fun y ↦ g ((c : 𝔸ᶠ[K]) * y)) ∈ finiteSchwartzBruhat K :=
      ⟨hg.1.comp_continuous (continuous_const_mul _), hg.2.comp_homeomorph (Homeomorph.smul c)⟩
    convert schwartzBruhatTensor_mem
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mixedMulLeft u) φ) hg' using 1
    funext x
    simp only [schwartzBruhatTensor, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
      Function.comp_apply, mixedMulLeft_apply]
    have h1 : (a • x).1 =
        ((IdeleGroup.toInfinite K a : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) * x.1 := rfl
    have h2 : (a • x).2 = (c : 𝔸ᶠ[K]) * x.2 := rfl
    have h3 : (u : mixedSpace K) = homeomorphMixedSpace K
        ((IdeleGroup.toInfinite K a : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) := rfl
    rw [h1, h2, homeomorphMixedSpace_mul, h3]
  | zero => exact zero_mem _
  | add G H _ _ hG hH => exact add_mem hG hH
  | smul r G _ hG => exact Submodule.smul_mem _ r hG

theorem summable_norm_smul_algebraMap (a : IdeleGroup K) {F : 𝔸[K] → ℂ}
    (hF : F ∈ schwartzBruhat K) : Summable fun ξ : K ↦ ‖F (a • algebraMap K 𝔸[K] ξ)‖ :=
  summable_norm_algebraMap_of_mem_schwartzBruhat (F := fun x ↦ F (a • x))
    (comp_smul_mem_schwartzBruhat a hF)

theorem summable_norm_adelicFourier_smul_algebraMap (a : IdeleGroup K) {F : 𝔸[K] → ℂ}
    (hF : F ∈ schwartzBruhat K) :
    Summable fun ξ : K ↦ ‖adelicFourier K F (a⁻¹ • algebraMap K 𝔸[K] ξ)‖ :=
  summable_norm_smul_algebraMap a⁻¹ (adelicFourier_mem_schwartzBruhat hF)

theorem tsum_smul_algebraMap_eq (a : IdeleGroup K) {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K) :
    ∑' ξ : K, F (a • algebraMap K 𝔸[K] ξ) =
      ((IdeleGroup.ideleModule K a : ℝ)⁻¹ : ℂ) *
        ∑' ξ : K, adelicFourier K F (a⁻¹ • algebraMap K 𝔸[K] ξ) := by
  rw [tsum_algebraMap_eq_tsum_adelicFourier (F := fun x ↦ F (a • x))
    (comp_smul_mem_schwartzBruhat a hF), ← tsum_mul_left]
  exact tsum_congr fun ξ ↦ adelicFourier_comp_smul a F _

end

end GroundTheory.Global
