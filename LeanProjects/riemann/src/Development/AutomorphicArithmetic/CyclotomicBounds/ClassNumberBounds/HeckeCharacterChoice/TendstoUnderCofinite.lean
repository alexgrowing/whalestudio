import Mathlib

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace KStar.Choice

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

noncomputable def complMap (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] : v.adicCompletion K →+* w.adicCompletion L :=
  ((adicCompletion.equiv L w).symm.toRingHom.comp
    (UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L)))
      (uniformContinuous_algebraMap_liesOver K L v w).continuous)).comp
    (adicCompletion.equiv K v).toRingHom

section

variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

theorem continuous_complMap : Continuous (complMap v w) :=
  (adicCompletion.continuous_ofCompletion L w).comp <|
    UniformSpace.Completion.continuous_map.comp (adicCompletion.continuous_toCompletion K v)

theorem complMap_algebraMap (x : K) :
    complMap v w (algebraMap K _ x) = algebraMap L _ (algebraMap K L x) := by
  apply adicCompletion.ext
  exact UniformSpace.Completion.mapRingHom_coe
    (uniformContinuous_algebraMap_liesOver K L v w).continuous (WithVal.toVal _ x)

theorem complMap_mem {x : v.adicCompletion K} (hx : x ∈ v.adicCompletionIntegers K) :
    complMap v w x ∈ w.adicCompletionIntegers L := by
  have hO : IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    Valued.isOpen_valuationSubring _
  have hC : IsClosed (w.adicCompletionIntegers L : Set (w.adicCompletion L)) :=
    Valued.isClosed_valuationSubring _
  have h := (denseRange_algebraMap K v).open_subset_closure_inter hO hx
  refine (hC.preimage (continuous_complMap v w)).closure_subset (closure_mono ?_ h)
  rintro _ ⟨h1, a, rfl⟩
  have h2 : v.valuation K a ≤ 1 := by
    rw [← valuedAdicCompletion_eq_valuation' v a]; exact h1
  rw [Set.mem_preimage, complMap_algebraMap]
  change Valued.v ((algebraMap K L a : L) : w.adicCompletion L) ≤ 1
  rw [valuedAdicCompletion_eq_valuation', ← valuation_liesOver L v w]
  exact pow_le_one' h2 _

end

instance liesOver_under (w : HeightOneSpectrum (𝓞 L)) :
    w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩

omit [NumberField K] [NumberField L] in
instance liesOver_comap (w : InfinitePlace L) : w.LiesOver (w.comap (algebraMap K L)) := ⟨rfl⟩

variable (K L)

theorem tendsto_under_cofinite :
    Filter.Tendsto (fun w : HeightOneSpectrum (𝓞 L) => w.under (𝓞 K)) Filter.cofinite
      Filter.cofinite := by
  refine Filter.Tendsto.cofinite_of_finite_preimage_singleton fun v => ?_
  have := v.isMaximal
  refine Set.Finite.of_finite_image (f := fun w => w.asIdeal)
    ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 L)).subset ?_)
    fun a _ b _ h => HeightOneSpectrum.ext h
  rintro _ ⟨w, hw, rfl⟩
  obtain rfl : w.under (𝓞 K) = v := hw
  exact ⟨w.isPrime, inferInstance⟩

noncomputable def finAdeleMap : FiniteAdeleRing (𝓞 K) K →+* FiniteAdeleRing (𝓞 L) L :=
  RestrictedProduct.mapAlongRingHom (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L)
    (B₁ := fun v => v.adicCompletionIntegers K) (B₂ := fun w => w.adicCompletionIntegers L)
    (fun w => w.under (𝓞 K)) (tendsto_under_cofinite K L)
    (fun w => complMap (w.under (𝓞 K)) w)
    (Filter.Eventually.of_forall fun w _ hx => complMap_mem _ w hx)

noncomputable def infAdeleMap : InfiniteAdeleRing K →+* InfiniteAdeleRing L :=
  RingHom.pi fun w : InfinitePlace L =>
    (LiesOver.completionMap (v := w.comap (algebraMap K L)) (w := w)).comp
      (Pi.evalRingHom (fun v : InfinitePlace K => v.Completion) _)

noncomputable def adeleMap : AdeleRing (𝓞 K) K →+* AdeleRing (𝓞 L) L :=
  RingHom.prodMap (infAdeleMap K L) (finAdeleMap K L)

theorem valued_complMap (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] (x : v.adicCompletion K) :
    Valued.v (complMap v w x) = Valued.v x ^ w.asIdeal.ramificationIdx (𝓞 K) := by
  by_cases hx : x = 0
  · subst hx
    have := w.isPrime
    rw [map_zero, map_zero, map_zero, zero_pow (Ideal.ramificationIdx_pos w.asIdeal (𝓞 K)).ne']
  have hx' : complMap v w x ≠ 0 := (map_ne_zero _).2 hx
  have h1 : {y | Valued.v y = Valued.v x} ∈ nhds x :=
    Valued.locally_const ((Valuation.ne_zero_iff _).2 hx)
  have h2 : complMap v w ⁻¹' {y | Valued.v y = Valued.v (complMap v w x)} ∈ nhds x :=
    (continuous_complMap v w).continuousAt.preimage_mem_nhds
      (Valued.locally_const ((Valuation.ne_zero_iff _).2 hx'))
  obtain ⟨a, ha1, ha2⟩ := (denseRange_algebraMap K v).mem_nhds (Filter.inter_mem h1 h2)
  have e1 : Valued.v (algebraMap K (v.adicCompletion K) a) = Valued.v x := ha1
  have e2 : Valued.v (complMap v w (algebraMap K (v.adicCompletion K) a)) =
      Valued.v (complMap v w x) := ha2
  have := w.isPrime
  rw [← e2, ← e1, complMap_algebraMap,
    ← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot]
  change Valued.v ((algebraMap K L a : L) : w.adicCompletion L) =
    Valued.v ((a : K) : v.adicCompletion K) ^ _
  rw [valuedAdicCompletion_eq_valuation', valuedAdicCompletion_eq_valuation',
    valuation_liesOver L v w]

theorem adeleMap_spec :
    Continuous (adeleMap K L) ∧ Function.Injective (adeleMap K L) ∧
      Continuous (infAdeleMap K L) ∧
      (∀ x : K, adeleMap K L (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) ∧
      ∀ x : K, infAdeleMap K L (algebraMap K _ x) = algebraMap L _ (algebraMap K L x) := by
  have hinf : Continuous (infAdeleMap K L) :=
    continuous_pi fun w => LiesOver.continuous_completionMap.comp (continuous_apply _)
  have hfin : Continuous (finAdeleMap K L) :=
    RestrictedProduct.mapAlong_continuous
      (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
      (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L)
      (A₁ := fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
      (A₂ := fun w => (w.adicCompletionIntegers L : Set (w.adicCompletion L)))
      (fun w => w.under (𝓞 K)) (tendsto_under_cofinite K L)
      (fun w => complMap (w.under (𝓞 K)) w)
      (Filter.Eventually.of_forall fun w x (hx : x ∈ (w.under (𝓞 K)).adicCompletionIntegers K) =>
        (complMap_mem _ w hx : _ ∈ w.adicCompletionIntegers L))
      (fun w => continuous_complMap _ w)
  have iinf : Function.Injective (infAdeleMap K L) := by
    intro x y h
    funext v
    obtain ⟨w, rfl⟩ := InfinitePlace.comap_surjective (K := L) v
    exact (LiesOver.completionMap (v := w.comap (algebraMap K L)) (w := w)).injective
      (congrFun h w)
  have ifin : Function.Injective (finAdeleMap K L) := by
    intro x y h
    refine FiniteAdeleRing.ext _ fun v => ?_
    obtain ⟨w, rfl⟩ : ∃ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 K) = v := by
      have := v.isMaximal
      obtain ⟨Q, hQ, hQv⟩ :=
        Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) v.asIdeal
      exact ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩,
        HeightOneSpectrum.ext hQv.over.symm⟩
    exact (complMap (w.under (𝓞 K)) w).injective (DFunLike.congr_fun h w)
  have ainf : ∀ x : K,
      infAdeleMap K L (algebraMap K _ x) = algebraMap L _ (algebraMap K L x) := by
    intro x
    funext w
    exact (LiesOver.completionMap_coe (v := w.comap (algebraMap K L)) (w := w)
      (WithAbs.toAbs _ x)).trans rfl
  refine ⟨hinf.prodMap hfin, iinf.prodMap ifin, hinf, fun x => Prod.ext (ainf x) ?_, ainf⟩
  exact FiniteAdeleRing.ext _ fun w => complMap_algebraMap _ w x

end KStar.Choice
