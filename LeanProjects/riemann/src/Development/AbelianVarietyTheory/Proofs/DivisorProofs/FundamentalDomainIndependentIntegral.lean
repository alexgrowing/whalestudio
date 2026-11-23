import Mathlib

open MeasureTheory

namespace GlobalTheory

section SymmetricUnfolding

variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]

theorem quasiMeasurePreserving_subgroup_mul (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant]
    (H : Subgroup G) (ν : Measure H) [SFinite ν] :
    Measure.QuasiMeasurePreserving (fun z : H × G => (z.1 : G) * z.2) (ν.prod μ) μ := by
  have hm : Measurable (Function.uncurry fun (p : H) (g : G) => (p : G) * g) :=
    (measurable_subtype_coe.comp measurable_fst).mul measurable_snd
  have h1 : MeasurePreserving (fun z : H × G => (id z.1, (z.1 : G) * z.2)) (ν.prod μ) (ν.prod μ) :=
    MeasurePreserving.skew_product (MeasurePreserving.id ν) hm
      (Filter.Eventually.of_forall fun p => map_mul_left_eq_self μ (p : G))
  exact Measure.quasiMeasurePreserving_snd.comp h1.quasiMeasurePreserving

theorem lintegral_mul_lintegral_subgroup_swap (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant]
    (H : Subgroup G) (ν : Measure H) [SFinite ν] (D : Set G) (hD : NullMeasurableSet D μ)
    (c : ENNReal) (hc : ∀ᵐ g ∂μ, ν {p : H | (p : G) * g ∈ D} = c)
    (f : G → ENNReal) (hf : AEMeasurable f μ) :
    c * ∫⁻ g, f g ∂μ = ∫⁻ p : H, ∫⁻ g, f g * D.indicator 1 ((p : G) * g) ∂μ ∂ν := by
  have hq := quasiMeasurePreserving_subgroup_mul μ H ν
  have hi : AEMeasurable (D.indicator (1 : G → ENNReal)) μ :=
    (measurable_const.aemeasurable : AEMeasurable (fun _ : G => (1 : ENNReal)) μ).indicator₀ hD
  have h1 : AEMeasurable (fun z : H × G => D.indicator (1 : G → ENNReal) ((z.1 : G) * z.2))
      (ν.prod μ) := hi.comp_quasiMeasurePreserving hq
  have h2 : AEMeasurable (fun z : H × G => f z.2) (ν.prod μ) :=
    hf.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have h3 : AEMeasurable (Function.uncurry fun (p : H) (g : G) =>
      f g * D.indicator (1 : G → ENNReal) ((p : G) * g)) (ν.prod μ) := h2.mul h1
  rw [lintegral_lintegral_swap h3, ← lintegral_const_mul'' c hf]
  have h4 := h1.aestronglyMeasurable.prodMk_right
  refine lintegral_congr_ae ?_
  filter_upwards [hc, h4] with g hg hg'
  have hg'' : AEMeasurable (fun p : H => D.indicator (1 : G → ENNReal) ((p : G) * g)) ν :=
    hg'.aemeasurable
  rw [lintegral_const_mul'' _ hg'', mul_comm, ← hg]
  congr 1
  have he : (fun p : H => D.indicator (1 : G → ENNReal) ((p : G) * g))
      = {p : H | (p : G) * g ∈ D}.indicator 1 := by
    funext p
    by_cases h : (p : G) * g ∈ D <;> simp [Set.indicator, h]
  have hn : NullMeasurableSet {p : H | (p : G) * g ∈ D} ν := by
    have h5 := hg''.nullMeasurable (measurableSet_singleton (1 : ENNReal))
    convert h5 using 1
    ext p
    by_cases h : (p : G) * g ∈ D <;> simp [Set.indicator, h]
  rw [he, lintegral_indicator_one₀ hn]

theorem const_mul_setLIntegral_eq_of_slice_measure :
    ∀ {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant] (H : Subgroup G) (ν : Measure H) [SFinite ν], MeasurePreserving (fun p : H => p⁻¹) ν ν → ∀ 𝓓₁ 𝓓₂ : Set G, NullMeasurableSet 𝓓₁ μ → NullMeasurableSet 𝓓₂ μ → ∀ c₁ c₂ : ENNReal, (∀ᵐ g ∂μ, ν {p : H | (p : G) * g ∈ 𝓓₁} = c₁) → (∀ᵐ g ∂μ, ν {p : H | (p : G) * g ∈ 𝓓₂} = c₂) → ∀ φ : G → ENNReal, AEMeasurable φ μ → (∀ p ∈ H, ∀ g, φ (p * g) = φ g) → c₂ * ∫⁻ g in 𝓓₁, φ g ∂μ = c₁ * ∫⁻ g in 𝓓₂, φ g ∂μ := by
  intro G _ _ _ _ μ _ _ H ν _ hinv D₁ D₂ hD₁ hD₂ c₁ c₂ h₁ h₂ φ hφ hinvφ
  rw [← lintegral_indicator₀ hD₁, ← lintegral_indicator₀ hD₂,
    lintegral_mul_lintegral_subgroup_swap μ H ν D₂ hD₂ c₂ h₂ _ (hφ.indicator₀ hD₁),
    lintegral_mul_lintegral_subgroup_swap μ H ν D₁ hD₁ c₁ h₁ _ (hφ.indicator₀ hD₂)]
  let e : H ≃ᵐ H :=
    { toEquiv := Equiv.inv H
      measurable_toFun := hinv.measurable
      measurable_invFun := hinv.measurable }
  have he : MeasurePreserving e ν ν := hinv
  rw [← he.lintegral_comp_emb e.measurableEmbedding]
  refine lintegral_congr fun p => ?_
  have hp : ((e p : H) : G) = (p : G)⁻¹ := rfl
  rw [hp, ← lintegral_mul_left_eq_self _ (p : G)]
  refine lintegral_congr fun g => ?_
  rw [inv_mul_cancel_left]
  by_cases a : (p : G) * g ∈ D₁ <;> by_cases b : g ∈ D₂ <;>
    simp [Set.indicator, a, b, hinvφ p p.2 g]

end SymmetricUnfolding

end GlobalTheory
