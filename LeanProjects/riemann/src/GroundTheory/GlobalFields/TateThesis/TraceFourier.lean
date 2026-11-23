import Mathlib
import GroundTheory.GlobalFields.TateThesis.TracePairing

namespace GroundTheory.Global

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module MeasureTheory
open scoped Classical ComplexConjugate RealInnerProductSpace FourierTransform Real ENNReal SchwartzMap

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

def selfDualMeasure : Measure (mixedSpace K) := (2 ^ nrComplexPlaces K : ℝ≥0∞) • volume

instance : (selfDualMeasure K).IsAddHaarMeasure :=
  Measure.IsAddHaarMeasure.smul _ (by simp) (by simp)

def mapComplexCoord (a : ℂ ≃L[ℝ] ℂ) : mixedSpace K ≃L[ℝ] mixedSpace K :=
  (ContinuousLinearEquiv.refl ℝ _).prodCongr (ContinuousLinearEquiv.piCongrRight fun _ => a)

omit [NumberField K] in
theorem mapComplexCoord_apply (a : ℂ ≃L[ℝ] ℂ) (x : mixedSpace K) :
    mapComplexCoord K a x = (x.1, fun w => a (x.2 w)) := rfl

theorem det_mapComplexCoord (a : ℂ ≃L[ℝ] ℂ) :
    LinearMap.det (mapComplexCoord K a : mixedSpace K →ₗ[ℝ] mixedSpace K) =
      LinearMap.det (a : ℂ →ₗ[ℝ] ℂ) ^ nrComplexPlaces K := by
  have : (mapComplexCoord K a : mixedSpace K →ₗ[ℝ] mixedSpace K) =
      LinearMap.prodMap LinearMap.id
        (LinearMap.pi fun w => (a : ℂ →ₗ[ℝ] ℂ) ∘ₗ LinearMap.proj w) :=
    LinearMap.ext fun _ => rfl
  rw [this, LinearMap.det_prodMap, LinearMap.det_id, one_mul, LinearMap.det_pi,
    Finset.prod_const, Finset.card_univ]

theorem measurePreserving_mapComplexCoord (a : ℂ ≃L[ℝ] ℂ)
    (ha : |LinearMap.det (a : ℂ →ₗ[ℝ] ℂ)| = 2) :
    MeasurePreserving (mapComplexCoord K a) (selfDualMeasure K) volume := by
  refine ⟨(mapComplexCoord K a).continuous.measurable, ?_⟩
  have hd := det_mapComplexCoord K a
  have hne : LinearMap.det (mapComplexCoord K a : mixedSpace K →ₗ[ℝ] mixedSpace K) ≠ 0 := by
    rw [hd]
    refine pow_ne_zero _ fun h => ?_
    rw [h, abs_zero] at ha
    norm_num at ha
  have hmap : Measure.map (mapComplexCoord K a) (volume : Measure (mixedSpace K)) =
      ENNReal.ofReal |(LinearMap.det (mapComplexCoord K a : mixedSpace K →ₗ[ℝ] mixedSpace K))⁻¹| •
        (volume : Measure (mixedSpace K)) :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hne
  rw [selfDualMeasure, Measure.map_smul, hmap, smul_smul, hd, abs_inv, abs_pow, ha,
    ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_ofNat, ENNReal.mul_inv_cancel (by simp) (by simp), one_smul]

def sqrtTwoSMulComplex : ℂ ≃L[ℝ] ℂ :=
  (LinearEquiv.smulOfNeZero ℝ ℂ (√2) (by positivity)).toContinuousLinearEquiv

theorem sqrtTwoSMulComplex_apply (z : ℂ) : sqrtTwoSMulComplex z = (√2 : ℝ) • z := rfl

theorem det_sqrtTwoSMulComplex : LinearMap.det (sqrtTwoSMulComplex : ℂ →ₗ[ℝ] ℂ) = 2 := by
  have : (sqrtTwoSMulComplex : ℂ →ₗ[ℝ] ℂ) = (√2 : ℝ) • LinearMap.id := LinearMap.ext fun _ => rfl
  rw [this, LinearMap.det_smul, LinearMap.det_id, mul_one, Complex.finrank_real_complex,
    Real.sq_sqrt (by norm_num)]

def sqrtTwoSMulConj : ℂ ≃L[ℝ] ℂ := Complex.conjCLE.trans sqrtTwoSMulComplex

theorem sqrtTwoSMulConj_apply (z : ℂ) : sqrtTwoSMulConj z = (√2 : ℝ) • conj z := rfl

theorem det_sqrtTwoSMulConj : LinearMap.det (sqrtTwoSMulConj : ℂ →ₗ[ℝ] ℂ) = -2 := by
  have : (sqrtTwoSMulConj : ℂ →ₗ[ℝ] ℂ) =
      (sqrtTwoSMulComplex : ℂ →ₗ[ℝ] ℂ) ∘ₗ Complex.conjAe.toLinearEquiv.toLinearMap :=
    LinearMap.ext fun _ => rfl
  rw [this, LinearMap.det_comp, det_sqrtTwoSMulComplex, Complex.det_conjAe]
  norm_num

def mixedToEuclidean : mixedSpace K ≃L[ℝ] euclidean.mixedSpace K :=
  (mapComplexCoord K sqrtTwoSMulComplex).trans (euclidean.toMixed K).symm

def mixedToEuclideanConj : mixedSpace K ≃L[ℝ] euclidean.mixedSpace K :=
  (mapComplexCoord K sqrtTwoSMulConj).trans (euclidean.toMixed K).symm

theorem measurePreserving_mixedToEuclidean :
    MeasurePreserving (mixedToEuclidean K) (selfDualMeasure K) volume :=
  (euclidean.volumePreserving_toMixed_symm K).comp
    (measurePreserving_mapComplexCoord K _ (by rw [det_sqrtTwoSMulComplex]; norm_num))

theorem measurePreserving_mixedToEuclideanConj :
    MeasurePreserving (mixedToEuclideanConj K) (selfDualMeasure K) volume :=
  (euclidean.volumePreserving_toMixed_symm K).comp
    (measurePreserving_mapComplexCoord K _ (by rw [det_sqrtTwoSMulConj]; norm_num))

theorem inner_toMixed_symm (x y : mixedSpace K) :
    ⟪(euclidean.toMixed K).symm x, (euclidean.toMixed K).symm y⟫ =
      ∑ w, x.1 w * y.1 w + ∑ w, (conj (x.2 w) * y.2 w).re := by
  simp [euclidean.toMixed, PiLp.inner_apply, real_inner_eq_re_inner]
  congr 1 <;> exact Finset.sum_congr rfl fun w _ => by ring

theorem mixedTraceForm_eq_inner (x y : mixedSpace K) :
    mixedTraceForm K x y = ⟪mixedToEuclidean K x, mixedToEuclideanConj K y⟫ := by
  rw [mixedTraceForm_apply', mixedToEuclidean, mixedToEuclideanConj,
    ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans_apply, inner_toMixed_symm]
  simp only [mapComplexCoord_apply, sqrtTwoSMulComplex_apply, sqrtTwoSMulConj_apply]
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  have hs : ((√2 : ℝ) : ℂ) * ((√2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  have : conj ((√2 : ℝ) • x.2 w) * ((√2 : ℝ) • conj (y.2 w)) =
      ((√2 : ℝ) : ℂ) * ((√2 : ℝ) : ℂ) * conj (x.2 w * y.2 w) := by
    rw [Complex.real_smul, Complex.real_smul, map_mul, map_mul, Complex.conj_ofReal]
    ring
  rw [this, hs]
  simp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def mixedFourier (f : mixedSpace K → E) : mixedSpace K → E :=
  VectorFourier.fourierIntegral 𝐞 (selfDualMeasure K) (mixedTraceForm K) f

def mixedFourierInv (f : mixedSpace K → E) : mixedSpace K → E :=
  VectorFourier.fourierIntegral 𝐞 (selfDualMeasure K) (-mixedTraceForm K) f

theorem mixedFourier_apply (f : mixedSpace K → E) (y : mixedSpace K) :
    mixedFourier K f y = ∫ x, 𝐞 (-mixedTraceForm K x y) • f x ∂selfDualMeasure K := rfl

theorem mixedFourierInv_apply (f : mixedSpace K → E) (x : mixedSpace K) :
    mixedFourierInv K f x = ∫ y, 𝐞 (mixedTraceForm K x y) • f y ∂selfDualMeasure K := by
  simp only [mixedFourierInv, VectorFourier.fourierIntegral, LinearMap.neg_apply, neg_neg,
    mixedTraceForm_comm K _ x]

theorem mixedFourier_eq (f : mixedSpace K → E) (y : mixedSpace K) :
    mixedFourier K f y = 𝓕 (f ∘ (mixedToEuclidean K).symm) (mixedToEuclideanConj K y) := by
  rw [mixedFourier_apply, Real.fourier_eq, ← (measurePreserving_mixedToEuclidean K).integral_comp
    (mixedToEuclidean K).toHomeomorph.measurableEmbedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [mixedTraceForm_eq_inner]

theorem mixedFourierInv_eq (f : mixedSpace K → E) (x : mixedSpace K) :
    mixedFourierInv K f x = 𝓕⁻ (f ∘ (mixedToEuclideanConj K).symm) (mixedToEuclidean K x) := by
  rw [mixedFourierInv_apply, Real.fourierInv_eq, ← (measurePreserving_mixedToEuclideanConj K).integral_comp
    (mixedToEuclideanConj K).toHomeomorph.measurableEmbedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp [mixedTraceForm_eq_inner, real_inner_comm]

def mixedFourierSchwartz : 𝓢(mixedSpace K, E) →L[ℂ] 𝓢(mixedSpace K, E) :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mixedToEuclideanConj K)).comp
    ((SchwartzMap.fourierTransformCLM ℂ).comp
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mixedToEuclidean K).symm))

theorem mixedFourierSchwartz_apply (f : 𝓢(mixedSpace K, E)) :
    ⇑(mixedFourierSchwartz K f) = mixedFourier K f := by
  funext y
  rw [mixedFourier_eq]
  rfl

variable [CompleteSpace E]

theorem mixedFourierInv_mixedFourier (f : 𝓢(mixedSpace K, E)) (x : mixedSpace K) :
    mixedFourierInv K (mixedFourier K f) x = f x := by
  set F : 𝓢(euclidean.mixedSpace K, E) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mixedToEuclidean K).symm f with hFdef
  have hF : (F : euclidean.mixedSpace K → E) = f ∘ (mixedToEuclidean K).symm := rfl
  have h1 : mixedFourier K f ∘ (mixedToEuclideanConj K).symm = 𝓕 (F : euclidean.mixedSpace K → E) := by
    funext v
    rw [Function.comp_apply, mixedFourier_eq, ContinuousLinearEquiv.apply_symm_apply, hF]
  have h2 : Integrable (𝓕 (F : euclidean.mixedSpace K → E)) := by
    rw [← SchwartzMap.fourier_coe]
    exact (𝓕 F).integrable
  rw [mixedFourierInv_eq, h1, F.continuous.fourierInv_fourier_eq F.integrable h2, hF,
    Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]

end

end GroundTheory.Global
