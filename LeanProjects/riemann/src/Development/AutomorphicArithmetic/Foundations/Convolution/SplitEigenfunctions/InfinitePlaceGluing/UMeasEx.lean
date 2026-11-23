import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global UpperTheory.ConvolutionTheory.R2

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

private lemma eq_one_of_mul {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a b : Γ}
    (ha : a ≤ 1) (hb : b ≤ 1) (h : a * b = 1) : a = 1 := by
  refine le_antisymm ha ?_
  have := mul_le_mul' (le_refl a) hb
  rwa [h, mul_one] at this

private lemma mem_UU_iff (t : IdeleGroup ℚ) :
    t ∈ UU ↔ IdeleGroup.toInfinite ℚ t = 1 ∧ IdeleGroup.toFinite ℚ t ∈ finiteIntegralUnits ℚ := by
  have hinv : ∀ v : H.P ℚ, Valued.v ((((IdeleGroup.toFinite ℚ t)⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
      FiniteAdeleRing (𝓞 ℚ) ℚ) v) * Valued.v (((IdeleGroup.toFinite ℚ t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
      FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1 := by
    intro v
    rw [← map_mul]
    have h := congrArg (fun x : FiniteAdeleRing (𝓞 ℚ) ℚ => x v) (Units.inv_mul (IdeleGroup.toFinite ℚ t))
    have h' : (((IdeleGroup.toFinite ℚ t)⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v *
        ((IdeleGroup.toFinite ℚ t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v = 1 := h
    rw [h', map_one]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨Units.ext h1, (mem_finiteIntegralUnits ℚ).2 fun v => ?_⟩
    have hv : Valued.v (((IdeleGroup.toFinite ℚ t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
        FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1 := h2 v
    have hi := hinv v
    rw [hv, mul_one] at hi
    exact ⟨(HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 hv.le,
      (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 hi.le⟩
  · rintro ⟨h1, h2⟩
    refine ⟨congrArg Units.val h1, fun v => ?_⟩
    obtain ⟨ha, hb⟩ := (mem_finiteIntegralUnits ℚ).1 h2 v
    exact eq_one_of_mul ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 ha)
      ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 hb) (by rw [mul_comm]; exact hinv v)

private lemma measurableSet_UU : MeasurableSet (UU : Set (IdeleGroup ℚ)) := by
  have h : (UU : Set (IdeleGroup ℚ)) = {t | IdeleGroup.toInfinite ℚ t = 1} ∩
      IdeleGroup.toFinite ℚ ⁻¹' (finiteIntegralUnits ℚ : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) := by
    ext t
    exact mem_UU_iff t
  rw [h]
  exact (isClosed_eq (IdeleGroup.continuous_toInfinite ℚ) continuous_const).measurableSet.inter
    ((isOpen_finiteIntegralUnits ℚ).preimage (IdeleGroup.continuous_toFinite ℚ)).measurableSet

private noncomputable def ef (x : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : IdeleGroup ℚ := (IdeleGroup.prodEquiv ℚ).symm (1, x)

private lemma measurable_ef : Measurable ef :=
  ((map_continuous (IdeleGroup.prodEquiv ℚ).symm).comp (continuous_const.prodMk continuous_id)).measurable

private lemma toInfinite_ef (x) : IdeleGroup.toInfinite ℚ (ef x) = 1 :=
  congrArg Prod.fst ((IdeleGroup.prodEquiv ℚ).apply_symm_apply (1, x))

private lemma toFinite_ef (x) : IdeleGroup.toFinite ℚ (ef x) = x :=
  congrArg Prod.snd ((IdeleGroup.prodEquiv ℚ).apply_symm_apply (1, x))

private lemma mul_ef {t : IdeleGroup ℚ} (h : IdeleGroup.toInfinite ℚ t = 1) (x) :
    t * ef x = ef (IdeleGroup.toFinite ℚ t * x) := by
  refine (IdeleGroup.prodEquiv ℚ).injective ?_
  rw [map_mul]
  refine Prod.ext ?_ ?_
  · change IdeleGroup.toInfinite ℚ t * IdeleGroup.toInfinite ℚ (ef x) = IdeleGroup.toInfinite ℚ (ef _)
    rw [h, toInfinite_ef, toInfinite_ef, one_mul]
  · change IdeleGroup.toFinite ℚ t * IdeleGroup.toFinite ℚ (ef x) = IdeleGroup.toFinite ℚ (ef _)
    rw [toFinite_ef, toFinite_ef]

theorem uMeasEx_of :
    UMeasEx := by
  have hU : MeasurableSet (finiteIntegralUnits ℚ : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :=
    (isOpen_finiteIntegralUnits ℚ).measurableSet
  refine ⟨⟨((finiteIdeleMeasure ℚ).restrict (finiteIntegralUnits ℚ)).map ef, ⟨?_⟩, ?_, ?_⟩⟩
  · rw [Measure.map_apply measurable_ef MeasurableSet.univ, Set.preimage_univ,
      Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, finiteIdeleMeasure_finiteIntegralUnits]
  · rw [Measure.map_apply measurable_ef measurableSet_UU.compl,
      Measure.restrict_apply (measurable_ef measurableSet_UU.compl)]
    convert measure_empty (μ := finiteIdeleMeasure ℚ)
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, SetLike.mem_coe,
      Set.mem_empty_iff_false, iff_false, not_and, not_not]
    intro hx hxU
    exact hx ((mem_UU_iff _).2 ⟨toInfinite_ef x, by rwa [toFinite_ef]⟩)
  · intro t ht
    obtain ⟨h1, h2⟩ := (mem_UU_iff t).1 ht
    have hg := (measurePreserving_mul_left (finiteIdeleMeasure ℚ) (IdeleGroup.toFinite ℚ t)).restrict_preimage hU
    have hpre : (fun x => IdeleGroup.toFinite ℚ t * x) ⁻¹'
        (finiteIntegralUnits ℚ : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) = finiteIntegralUnits ℚ := by
      ext x
      exact (finiteIntegralUnits ℚ).mul_mem_cancel_left h2
    rw [hpre] at hg
    have hf : Measurable fun x : IdeleGroup ℚ => (t * x : (A ℚ)ˣ) :=
      (continuous_const.mul continuous_id).measurable
    rw [Measure.map_map hf measurable_ef]
    have hc : (fun x : IdeleGroup ℚ => (t * x : (A ℚ)ˣ)) ∘ ef = ef ∘ fun x => IdeleGroup.toFinite ℚ t * x := by
      funext x
      exact mul_ef h1 x
    rw [hc, ← Measure.map_map measurable_ef hg.measurable, hg.map_eq]

end UpperTheory.ConvolutionTheory.RankTwoDescent
