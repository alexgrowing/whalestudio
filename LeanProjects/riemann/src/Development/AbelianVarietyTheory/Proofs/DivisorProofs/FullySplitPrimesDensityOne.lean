import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.TrivialOfDensityOne
import GroundTheory.GlobalFields.TateThesis.DegreeOneDensity
open NumberField IsDedekindDomain

namespace GlobalTheory.DensitySplit

open Filter Topology Set GroundTheory.Global

theorem finite_under_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (T : Finset (HeightOneSpectrum (𝓞 F))) :
    {w : HeightOneSpectrum (𝓞 E) | w.under (𝓞 F) ∈ T}.Finite := by
  have : {w : HeightOneSpectrum (𝓞 E) | w.under (𝓞 F) ∈ T} ⊆
      ⋃ v ∈ (T : Set (HeightOneSpectrum (𝓞 F))),
        {w : HeightOneSpectrum (𝓞 E) | w.asIdeal ∣ v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))} := by
    intro w hw
    refine Set.mem_biUnion (x := w.under (𝓞 F)) hw ?_
    show w.asIdeal ∣ _
    rw [Ideal.dvd_iff_le]
    exact Ideal.map_le_iff_le_comap.mpr le_rfl
  refine Set.Finite.subset (Set.Finite.biUnion T.finite_toSet fun v _ => ?_) this
  refine Ideal.finite_factors ?_
  exact (Ideal.map_eq_bot_iff_of_injective
      (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))).not.mpr v.ne_bot

theorem algebraMap_int_ratIntegers_surjective : Function.Surjective (algebraMap ℤ (𝓞 ℚ)) := by
  intro x
  refine ⟨Rat.ringOfIntegersEquiv x, ?_⟩
  have : algebraMap ℤ (𝓞 ℚ) = (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) := RingHom.ext_int _ _
  rw [this]
  exact Rat.ringOfIntegersEquiv.symm_apply_apply x

theorem ncard_primesOver_int {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (hw : SplitsCompletely E (w.under (𝓞 ℚ))) :
    ((w.asIdeal.under ℤ).primesOver (𝓞 E)).ncard = Module.finrank ℚ E := by
  rw [← ncard_primesOver_of_splitsCompletely E hw]
  congr 1
  ext P
  have hinj : Function.Injective (Ideal.comap (algebraMap ℤ (𝓞 ℚ))) :=
    Ideal.comap_injective_of_surjective _ algebraMap_int_ratIntegers_surjective
  simp only [Ideal.primesOver, Set.mem_setOf_eq]
  refine and_congr Iff.rfl ?_
  rw [Ideal.liesOver_iff, Ideal.liesOver_iff]
  show w.asIdeal.under ℤ = P.under ℤ ↔ w.asIdeal.under (𝓞 ℚ) = P.under (𝓞 ℚ)
  rw [← Ideal.under_under (B := 𝓞 ℚ) w.asIdeal, ← Ideal.under_under (B := 𝓞 ℚ) P]
  exact hinj.eq_iff

theorem hasDirichletDensity_one_of_subset {K : Type} [Field K] [NumberField K]
    {A B : Set (HeightOneSpectrum (𝓞 K))} (hAB : A ⊆ B) (hA : A.HasDirichletDensity 1) :
    B.HasDirichletDensity 1 := by
  unfold NumberField.Set.HasDirichletDensity at hA ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hA tendsto_const_nhds ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
    exact div_le_div_of_nonneg_right (primeIdealZetaSum_mono hAB hs)
      (Set.primeIdealZetaSum_nonneg _ s)
  · filter_upwards [self_mem_nhdsWithin,
      (tendsto_primeIdealZetaSum_univ_atTop K).eventually_gt_atTop 0] with s (hs : 1 < s) hpos
    exact div_le_one_of_le₀ (primeIdealZetaSum_mono (subset_univ B) hs) hpos.le

theorem hasDirichletDensity_splitsFully (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (hG : IsGalois ℚ E) (T : Finset (HeightOneSpectrum (𝓞 F))) :
    NumberField.Set.HasDirichletDensity {w : HeightOneSpectrum (𝓞 E) | w.under (𝓞 F) ∉ T ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SplitsFully E (w.under (𝓞 F))} 1 := by
  set Spl := {v : HeightOneSpectrum (𝓞 ℚ) | SplitsCompletely E v}
  have hT : ∀ v ∈ Spl, SplitsCompletely E v := fun v hv => hv
  have hn : (Module.finrank ℚ E : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := E)).ne'
  have h1 : (primesAbove E Spl).HasDirichletDensity 1 := by
    have := (hasDirichletDensity_primesAbove_iff hT _).mpr
      (hasDirichletDensity_setOf_splitsCompletely ℚ E)
    rwa [mul_one_div_cancel hn] at this
  set Bad := {w : HeightOneSpectrum (𝓞 E) | w.under (𝓞 F) ∈ T}
  have h2 : (primesAbove E Spl \ Bad).HasDirichletDensity 1 := by
    refine (hasDirichletDensity_iff_of_subset_of_isBoundedUnder diff_subset
      (isBoundedUnder_primeIdealZetaSum_of_finite ((finite_under_mem (E := E) T).subset ?_)) 1).mpr h1
    intro w hw
    by_contra h
    exact hw.2 ⟨hw.1, h⟩
  refine hasDirichletDensity_one_of_subset ?_ h2
  rintro w ⟨hw, hbad⟩
  refine ⟨hbad, ?_⟩
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SplitsFully
  have : (w.under (𝓞 F)).asIdeal.under ℤ = w.asIdeal.under ℤ := Ideal.under_under w.asIdeal
  rw [this]
  exact ncard_primesOver_int w hw

end GlobalTheory.DensitySplit
