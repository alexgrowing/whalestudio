import Mathlib
import GroundTheory.GlobalFields.Adele.Compact
import GroundTheory.GlobalFields.Adele.Discrete
import GroundTheory.GlobalFields.Adele.Topology
import GroundTheory.GlobalFields.TateThesis.TraceFourier
import GroundTheory.GlobalFields.TateThesis.AdeleMeasurable

namespace GroundTheory.Global

open NumberField NumberField.mixedEmbedding IsDedekindDomain MeasureTheory Measure
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise Classical

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

theorem countable_numberField : Countable K :=
  (Module.finBasis ℚ K).equivFun.toEquiv.countable_iff.2 inferInstance

instance sigmaCompactSpace_finiteAdeleRing : SigmaCompactSpace (FiniteAdeleRing (𝓞 K) K) := by
  have := countable_numberField K
  rw [← isSigmaCompact_univ_iff]
  have hU : (Set.univ : Set (FiniteAdeleRing (𝓞 K) K)) =
      ⋃ k : K, algebraMap K (FiniteAdeleRing (𝓞 K) K) k +ᵥ
        (integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)) := by
    refine (Set.eq_univ_of_forall fun a ↦ ?_).symm
    obtain ⟨k, hk⟩ := exists_sub_mem_integralFiniteAdeles a
    refine Set.mem_iUnion.2 ⟨k, ⟨a - algebraMap K _ k, hk, ?_⟩⟩
    simp
  rw [hU]
  exact isSigmaCompact_iUnion_of_isCompact _ fun k ↦
    (isCompact_integralFiniteAdeles K).vadd _

def integralFiniteAdelesPositiveCompacts : TopologicalSpace.PositiveCompacts (FiniteAdeleRing (𝓞 K) K) where
  carrier := integralFiniteAdeles (𝓞 K) K
  isCompact' := isCompact_integralFiniteAdeles K
  interior_nonempty' := by
    rw [isOpen_integralFiniteAdeles.interior_eq]
    exact ⟨0, Subring.zero_mem _⟩

theorem coe_integralFiniteAdelesPositiveCompacts :
    (integralFiniteAdelesPositiveCompacts K : Set (FiniteAdeleRing (𝓞 K) K)) =
      integralFiniteAdeles (𝓞 K) K :=
  rfl

def finiteAdeleMeasure : Measure (FiniteAdeleRing (𝓞 K) K) :=
  (NNReal.sqrt ‖discr K‖₊)⁻¹ • addHaarMeasure (integralFiniteAdelesPositiveCompacts K)

theorem sqrt_discr_ne_zero : NNReal.sqrt ‖discr K‖₊ ≠ 0 := by
  rw [Ne, NNReal.sqrt_eq_zero, nnnorm_eq_zero]
  exact discr_ne_zero K

instance : (finiteAdeleMeasure K).IsAddHaarMeasure := by
  rw [finiteAdeleMeasure]
  exact IsAddHaarMeasure.nnreal_smul _ (inv_ne_zero (sqrt_discr_ne_zero K))

instance : (finiteAdeleMeasure K).Regular := by
  rw [finiteAdeleMeasure]
  infer_instance

theorem finiteAdeleMeasure_integralFiniteAdeles :
    finiteAdeleMeasure K (integralFiniteAdeles (𝓞 K) K) = ((NNReal.sqrt ‖discr K‖₊)⁻¹ : ℝ≥0) := by
  rw [finiteAdeleMeasure, Measure.smul_apply, ← coe_integralFiniteAdelesPositiveCompacts,
    addHaarMeasure_self, ENNReal.smul_def, smul_eq_mul, mul_one]

def measurableEquivMixedSpace : InfiniteAdeleRing K ≃ᵐ mixedSpace K :=
  (homeomorphMixedSpace K).toMeasurableEquiv

theorem measurableEquivMixedSpace_apply (x : InfiniteAdeleRing K) :
    measurableEquivMixedSpace K x = homeomorphMixedSpace K x :=
  rfl

def addEquivMixedSpace : InfiniteAdeleRing K ≃+ mixedSpace K where
  __ := (homeomorphMixedSpace K).toEquiv
  map_add' x y := by
    change homeomorphMixedSpace K (x + y) = homeomorphMixedSpace K x + homeomorphMixedSpace K y
    simp only [homeomorphMixedSpace_apply, map_add]

def infiniteAdeleMeasure : Measure (InfiniteAdeleRing K) :=
  (selfDualMeasure K).map (measurableEquivMixedSpace K).symm

instance : (infiniteAdeleMeasure K).IsAddHaarMeasure :=
  (addEquivMixedSpace K).symm.isAddHaarMeasure_map (selfDualMeasure K)
    (homeomorphMixedSpace K).symm.continuous (homeomorphMixedSpace K).continuous

theorem measurePreserving_measurableEquivMixedSpace :
    MeasurePreserving (measurableEquivMixedSpace K) (infiniteAdeleMeasure K) (selfDualMeasure K) :=
  MeasurePreserving.symm _ (⟨(measurableEquivMixedSpace K).symm.measurable, rfl⟩ :
    MeasurePreserving (measurableEquivMixedSpace K).symm (selfDualMeasure K) (infiniteAdeleMeasure K))

def adeleMeasure : Measure 𝔸[K] :=
  (infiniteAdeleMeasure K).prod (finiteAdeleMeasure K)

instance : (adeleMeasure K).IsAddHaarMeasure :=
  inferInstanceAs ((infiniteAdeleMeasure K).prod (finiteAdeleMeasure K)).IsAddHaarMeasure

theorem adeleMeasure_prod (A : Set (InfiniteAdeleRing K)) (B : Set (FiniteAdeleRing (𝓞 K) K)) :
    adeleMeasure K (A ×ˢ B) = infiniteAdeleMeasure K A * finiteAdeleMeasure K B :=
  Measure.prod_prod A B

theorem measurableSet_fundamentalSet : MeasurableSet (fundamentalSet K) :=
  ((homeomorphMixedSpace K).measurable (ZSpan.fundamentalDomain_measurableSet _)).prod
    isOpen_integralFiniteAdeles.measurableSet

theorem infiniteAdeleMeasure_fundamentalSetInfinite :
    infiniteAdeleMeasure K (fundamentalSetInfinite K) = (NNReal.sqrt ‖discr K‖₊ : ℝ≥0∞) := by
  change infiniteAdeleMeasure K ((measurableEquivMixedSpace K) ⁻¹'
    ZSpan.fundamentalDomain (latticeBasis K)) = _
  rw [(measurePreserving_measurableEquivMixedSpace K).measure_preimage_equiv, selfDualMeasure,
    Measure.smul_apply, volume_fundamentalDomain_latticeBasis, smul_eq_mul, ← mul_assoc, ← mul_pow,
    ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow, one_mul]

theorem adeleMeasure_fundamentalSet : adeleMeasure K (fundamentalSet K) = 1 := by
  rw [fundamentalSet, adeleMeasure_prod, infiniteAdeleMeasure_fundamentalSetInfinite,
    finiteAdeleMeasure_integralFiniteAdeles, ← ENNReal.coe_mul,
    mul_inv_cancel₀ (sqrt_discr_ne_zero K), ENNReal.coe_one]

theorem isAddFundamentalDomain_fundamentalSet :
    IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 K) K) (fundamentalSet K)
      (adeleMeasure K) := by
  refine IsAddFundamentalDomain.mk' (measurableSet_fundamentalSet K).nullMeasurableSet fun x ↦ ?_
  obtain ⟨k, hk, huniq⟩ := existsUnique_sub_mem_fundamentalSet K x
  refine ⟨⟨algebraMap K 𝔸[K] (-k), -k, rfl⟩, ?_, ?_⟩
  · change algebraMap K 𝔸[K] (-k) + x ∈ fundamentalSet K
    rwa [map_neg, neg_add_eq_sub]
  · rintro ⟨_, k', rfl⟩ h
    change algebraMap K 𝔸[K] k' + x ∈ fundamentalSet K at h
    have hk' : -k' = k := huniq (-k') (by
      change x - algebraMap K 𝔸[K] (-k') ∈ fundamentalSet K
      rwa [map_neg, sub_neg_eq_add, add_comm])
    refine Subtype.ext ?_
    change algebraMap K 𝔸[K] k' = algebraMap K 𝔸[K] (-k)
    rw [← hk', neg_neg]

end

end GroundTheory.Global
