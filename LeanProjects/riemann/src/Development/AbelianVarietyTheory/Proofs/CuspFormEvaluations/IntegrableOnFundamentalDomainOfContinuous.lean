import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TiledBoundaries.TileIntegral

namespace GlobalTheory

open MeasureTheory

section

variable {V κ : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Fintype κ]

theorem setIntegral_fundamentalDomain_add_right {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (μ : Measure V) [μ.IsAddHaarMeasure] (b : Module.Basis κ ℝ V)
    (f : V → E) (hb : ∀ γ ∈ Submodule.span ℤ (Set.range b), ∀ v, f (v + γ) = f v) (a : V) :
    ∫ v in ZSpan.fundamentalDomain b, f (v + a) ∂μ = ∫ v in ZSpan.fundamentalDomain b, f v ∂μ := by
  have hA := ZSpan.isAddFundamentalDomain' b μ
  have hT : IsAddFundamentalDomain (Submodule.span ℤ (Set.range b)).toAddSubgroup
      ((fun x => x - a) ⁻¹' ZSpan.fundamentalDomain b) μ := by
    refine IsAddFundamentalDomain.mk' ?_ fun x => ?_
    · exact ((ZSpan.fundamentalDomain_measurableSet b).preimage
        (measurable_sub_const a)).nullMeasurableSet
    · obtain ⟨g, hg, hu⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain b (x - a)
      refine ⟨⟨g, g.2⟩, ?_, ?_⟩
      · change (g : V) + x - a ∈ ZSpan.fundamentalDomain b
        rw [add_sub_assoc]; exact hg
      · rintro ⟨y, hy⟩ h
        change y + x - a ∈ ZSpan.fundamentalDomain b at h
        rw [add_sub_assoc] at h
        exact Subtype.ext (congrArg Subtype.val (hu ⟨y, hy⟩ h))
  have hper : ∀ (g : (Submodule.span ℤ (Set.range b)).toAddSubgroup) (x : V),
      f (g +ᵥ x) = f x := by
    intro g x
    change f ((g : V) + x) = f x
    rw [add_comm]
    exact hb g g.2 x
  rw [hA.setIntegral_eq hT hper]
  have e := (measurePreserving_sub_right μ a).setIntegral_preimage_emb
    (measurableEmbedding_subRight a) (fun y => f (y + a)) (ZSpan.fundamentalDomain b)
  simp only [sub_add_cancel] at e
  exact e.symm

theorem integrableOn_fundamentalDomain_of_continuous {E : Type} [NormedAddCommGroup E]
    (μ : Measure V) [μ.IsAddHaarMeasure] (b : Module.Basis κ ℝ V)
    (f : V → E) (hf : Continuous f) : IntegrableOn f (ZSpan.fundamentalDomain b) μ :=
  (hf.continuousOn.integrableOn_compact
    (ZSpan.fundamentalDomain_isBounded b).isCompact_closure).mono_set subset_closure

end

theorem average_fundamentalDomain_eq_real {V κ κ' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [Fintype κ] [Fintype κ'] (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure]
    (b : Module.Basis κ ℝ V) (b' : Module.Basis κ' ℝ V)
    (f : V → ℝ) (hf : Continuous f)
    (hb : ∀ γ ∈ Submodule.span ℤ (Set.range b), ∀ v, f (v + γ) = f v)
    (hle : Submodule.span ℤ (Set.range b') ≤ Submodule.span ℤ (Set.range b)) (a : V) :
    ⨍ v in ZSpan.fundamentalDomain b', f (v + a) ∂μ =
      ⨍ v in ZSpan.fundamentalDomain b, f v ∂μ := by
  have h1 : ⨍ v in ZSpan.fundamentalDomain b', f (v + a) ∂μ =
      ⨍ v in ZSpan.fundamentalDomain b', f v ∂μ := by
    rw [setAverage_eq, setAverage_eq,
      setIntegral_fundamentalDomain_add_right μ b' f (fun γ hγ => hb γ (hle hγ)) a]
  rw [h1, ← ZSpan.fundamentalDomain_reindex b' (b'.indexEquiv b)]
  refine ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.tile_average μ _ b ?_ f hf hb
  rwa [Module.Basis.range_reindex]

end GlobalTheory
