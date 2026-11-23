import Mathlib
import GroundTheory.GlobalFields.TateThesis.AdeleMeasure
import GroundTheory.GlobalFields.TateThesis.FiniteAdeleScaling
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms

namespace GroundTheory.Global

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace IsDedekindDomain
  MeasureTheory Measure
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise Classical

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem det_mulLeft_mixedSpace (c : mixedSpace K) :
    LinearMap.det (LinearMap.mulLeft ℝ c) =
      (∏ w, c.1 w) * ∏ w, Complex.normSq (c.2 w) := by
  have h : LinearMap.mulLeft ℝ c = LinearMap.prodMap
      (LinearMap.pi fun w ↦ LinearMap.mulLeft ℝ (c.1 w) ∘ₗ LinearMap.proj w)
      (LinearMap.pi fun w ↦ LinearMap.mulLeft ℝ (c.2 w) ∘ₗ LinearMap.proj w) :=
    LinearMap.ext fun _ ↦ rfl
  rw [h, LinearMap.det_prodMap, LinearMap.det_pi, LinearMap.det_pi]
  congr 1
  · exact Finset.prod_congr rfl fun w _ ↦ LinearMap.det_mulLeft _
  · refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [← Algebra.norm_complex_apply, Algebra.norm_apply]
    rfl

theorem abs_det_mulLeft_mixedSpace (c : mixedSpace K) :
    |LinearMap.det (LinearMap.mulLeft ℝ c)| = mixedEmbedding.norm c := by
  rw [det_mulLeft_mixedSpace, mixedEmbedding.norm_apply, prod_eq_prod_mul_prod, abs_mul,
    Finset.abs_prod, Finset.abs_prod]
  congr 1
  · refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [mult_isReal, pow_one, normAtPlace_apply_of_isReal w.2, Real.norm_eq_abs]
  · refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [mult_isComplex, normAtPlace_apply_of_isComplex w.2, abs_of_nonneg (Complex.normSq_nonneg _),
      Complex.normSq_eq_norm_sq]

omit [NumberField K] in

theorem normAtPlace_homeomorphMixedSpace (x : InfiniteAdeleRing K) (w : InfinitePlace K) :
    normAtPlace w (homeomorphMixedSpace K x) = ‖x w‖ := by
  rcases w.isReal_or_isComplex with hw | hw
  · rw [normAtPlace_apply_of_isReal hw, homeomorphMixedSpace_apply,
      InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    exact (Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) _
  · rw [normAtPlace_apply_of_isComplex hw, homeomorphMixedSpace_apply,
      InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    exact (Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _

theorem norm_homeomorphMixedSpace (x : InfiniteAdeleRing K) :
    mixedEmbedding.norm (homeomorphMixedSpace K x) = ‖x‖ := by
  rw [mixedEmbedding.norm_apply, InfiniteAdeleRing.norm_def]
  simp only [normAtPlace_homeomorphMixedSpace]

omit [NumberField K] in
theorem homeomorphMixedSpace_mul (x y : InfiniteAdeleRing K) :
    homeomorphMixedSpace K (x * y) = homeomorphMixedSpace K x * homeomorphMixedSpace K y := by
  simp only [homeomorphMixedSpace_apply, map_mul]

variable (K) in

theorem infiniteAdeleMeasure_apply (E : Set (InfiniteAdeleRing K)) :
    infiniteAdeleMeasure K E = selfDualMeasure K (homeomorphMixedSpace K '' E) := by
  rw [infiniteAdeleMeasure, MeasurableEquiv.map_apply]
  exact congrArg _ ((measurableEquivMixedSpace K).image_eq_preimage_symm E).symm

theorem infiniteAdeleMeasure_smul (a : (InfiniteAdeleRing K)ˣ) (E : Set (InfiniteAdeleRing K)) :
    infiniteAdeleMeasure K (a • E) =
      ENNReal.ofReal ‖(a : InfiniteAdeleRing K)‖ * infiniteAdeleMeasure K E := by
  rw [infiniteAdeleMeasure_apply, infiniteAdeleMeasure_apply,
    ← norm_homeomorphMixedSpace, ← abs_det_mulLeft_mixedSpace, ← addHaar_image_linearMap]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_smul_set, Units.smul_def, smul_eq_mul, LinearMap.mulLeft_apply]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, (homeomorphMixedSpace_mul _ _).symm⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, homeomorphMixedSpace_mul _ _⟩

theorem map_mul_left_infiniteAdeleMeasure (b : (InfiniteAdeleRing K)ˣ) :
    (infiniteAdeleMeasure K).map (fun y ↦ (b : InfiniteAdeleRing K) * y) =
      ENNReal.ofReal ‖((b⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)‖ •
        infiniteAdeleMeasure K := by
  ext S hS
  rw [map_apply (continuous_const_mul _).measurable hS, Measure.smul_apply, smul_eq_mul,
    ← infiniteAdeleMeasure_smul]
  congr 1
  exact Set.preimage_smul b S

theorem map_mul_left_finiteAdeleMeasure (b : (𝔸ᶠ[K])ˣ) :
    (finiteAdeleMeasure K).map (fun y ↦ (b : 𝔸ᶠ[K]) * y) =
      ((∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖((b⁻¹ : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) v‖₊ : ℝ≥0) : ℝ≥0∞) •
        finiteAdeleMeasure K := by
  ext S hS
  rw [map_apply (continuous_const_mul _).measurable hS, Measure.smul_apply, smul_eq_mul,
    ← finiteAdeleMeasure_smul]
  congr 1
  exact Set.preimage_smul b S

theorem coe_finprod_nnnorm (u : (𝔸ᶠ[K])ˣ) :
    ((∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(u : 𝔸ᶠ[K]) v‖₊ : ℝ≥0) : ℝ) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(u : 𝔸ᶠ[K]) v‖ := by
  set S := (finite_mulSupport_nnnorm_units u).toFinset
  have hS : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 K) ↦ ‖(u : 𝔸ᶠ[K]) v‖₊) ⊆ S := by
    simp [S]
  have hS' : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 K) ↦ ‖(u : 𝔸ᶠ[K]) v‖) ⊆ S := by
    intro v hv
    apply hS
    intro h
    apply hv
    simpa using congrArg NNReal.toReal h
  rw [finprod_eq_prod_of_mulSupport_subset _ hS, finprod_eq_prod_of_mulSupport_subset _ hS',
    NNReal.coe_prod]
  rfl

theorem map_prodMap_mul_left_prod (b : (InfiniteAdeleRing K)ˣ) (c : (𝔸ᶠ[K])ˣ) :
    ((infiniteAdeleMeasure K).prod (finiteAdeleMeasure K)).map
      (Prod.map (fun y ↦ (b : InfiniteAdeleRing K) * y) (fun y ↦ (c : 𝔸ᶠ[K]) * y)) =
      (ENNReal.ofReal ‖((b⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)‖ *
        ((∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖((c⁻¹ : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) v‖₊ : ℝ≥0) : ℝ≥0∞)) •
        (infiniteAdeleMeasure K).prod (finiteAdeleMeasure K) := by
  rw [← map_prod_map _ _ (continuous_const_mul _).measurable (continuous_const_mul _).measurable,
    map_mul_left_infiniteAdeleMeasure, map_mul_left_finiteAdeleMeasure, prod_smul_left,
    prod_smul_right, smul_smul]

theorem map_smul_adeleMeasure (a : IdeleGroup K) :
    (adeleMeasure K).map (fun x ↦ a • x) =
      ENNReal.ofReal ((IdeleGroup.ideleModule K a : ℝ))⁻¹ • adeleMeasure K := by
  have hsplit : (fun x : 𝔸[K] ↦ a • x) = Prod.map
      (fun y ↦ ((IdeleGroup.toInfinite K a : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) * y)
      (fun y ↦ ((IdeleGroup.toFinite K a : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) * y) :=
    funext fun _ ↦ rfl
  have hc : ENNReal.ofReal ‖(((IdeleGroup.toInfinite K a)⁻¹ : (InfiniteAdeleRing K)ˣ) :
      InfiniteAdeleRing K)‖ * ((∏ᶠ v : HeightOneSpectrum (𝓞 K),
        ‖(((IdeleGroup.toFinite K a)⁻¹ : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) v‖₊ : ℝ≥0) : ℝ≥0∞) =
      ENNReal.ofReal ((IdeleGroup.ideleModule K a : ℝ))⁻¹ := by
    have hnn : (0 : ℝ) ≤ ‖((IdeleGroup.toInfinite K a⁻¹ : (InfiniteAdeleRing K)ˣ) :
        InfiniteAdeleRing K)‖ := by
      rw [InfiniteAdeleRing.norm_def]
      exact Finset.prod_nonneg fun w _ ↦ pow_nonneg (norm_nonneg _) _
    rw [← map_inv, ← map_inv, ← ENNReal.ofReal_coe_nnreal, coe_finprod_nnnorm,
      ← ENNReal.ofReal_mul hnn, ← Positive.coe_inv, ← map_inv,
      IdeleGroup.ideleModule_apply]
    rfl
  rw [hsplit, ← hc]
  exact map_prodMap_mul_left_prod _ _

theorem adeleMeasure_smul (a : IdeleGroup K) (E : Set 𝔸[K]) :
    adeleMeasure K (a • E) = ENNReal.ofReal (IdeleGroup.ideleModule K a : ℝ) * adeleMeasure K E := by
  have hE : ((adeleMeasure K).map (fun x ↦ a⁻¹ • x)) E =
      (ENNReal.ofReal ((IdeleGroup.ideleModule K a⁻¹ : ℝ))⁻¹ • adeleMeasure K) E := by
    rw [map_smul_adeleMeasure]
  have hm := (Homeomorph.smul a⁻¹).toMeasurableEquiv.map_apply (μ := adeleMeasure K) E
  rw [show ⇑(Homeomorph.smul a⁻¹).toMeasurableEquiv = fun x : 𝔸[K] ↦ a⁻¹ • x from rfl] at hm
  rw [hm, Measure.smul_apply, smul_eq_mul] at hE
  have h := hE
  rw [← Set.preimage_smul_inv]
  convert h using 2
  rw [map_inv, Positive.coe_inv, inv_inv]

end

end GroundTheory.Global
