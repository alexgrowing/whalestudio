import Mathlib

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS

section KDC

variable {E X : Type*} [TopologicalSpace E] [PolishSpace E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]

def kdNu (m : Measure X) (f : E → X) (U : Set E) : Measure E :=
  Measure.map (Subtype.val : U → E) (Measure.comap (fun x : U => f x) m)

lemma kdNu_apply {m : Measure X} {f : E → X} {U : Set E} (hU : MeasurableSet U) (hf : ContinuousOn f U)
    (hinj : InjOn f U) {A : Set E} (hA : MeasurableSet A) : kdNu m f U A = m (f '' (A ∩ U)) := by
  have hI : Function.Injective (fun x : U => f x) := fun a b h => Subtype.ext (hinj a.2 b.2 h)
  have hM : ∀ s : Set U, MeasurableSet s → MeasurableSet ((fun x : U => f x) '' s) := by
    intro s hs
    have e : (fun x : U => f x) '' s = f '' (Subtype.val '' s) := by rw [image_image]
    rw [e]
    have hsub : Subtype.val '' s ⊆ U := by rintro _ ⟨x, _, rfl⟩; exact x.2
    exact (hU.subtype_image hs).image_of_continuousOn_injOn (hf.mono hsub) (hinj.mono hsub)
  rw [kdNu, Measure.map_apply measurable_subtype_coe hA,
    Measure.comap_apply _ hI hM _ (measurable_subtype_coe hA)]
  congr 1
  ext y
  constructor
  · rintro ⟨⟨x, hx⟩, hxA, rfl⟩; exact ⟨x, ⟨hxA, hx⟩, rfl⟩
  · rintro ⟨x, ⟨hxA, hx⟩, rfl⟩; exact ⟨⟨x, hx⟩, hxA, rfl⟩

lemma kdNu_finite {m : Measure X} [IsFiniteMeasure m] {f : E → X} {U : Set E} (hU : MeasurableSet U)
    (hf : ContinuousOn f U) (hinj : InjOn f U) : IsFiniteMeasure (kdNu m f U) :=
  ⟨by rw [kdNu_apply hU hf hinj MeasurableSet.univ]; exact measure_lt_top _ _⟩

lemma kdNu_le {m : Measure X} {f : E → X} {U : Set E} (hU : MeasurableSet U) (hf : ContinuousOn f U)
    (hinj : InjOn f U) (lam : Measure E) (c : ℝ≥0∞)
    (h : ∀ A ⊆ U, MeasurableSet A → m (f '' A) ≤ c * lam A) : kdNu m f U ≤ c • lam.restrict U := by
  refine Measure.le_iff.2 fun A hA => ?_
  rw [kdNu_apply hU hf hinj hA, Measure.smul_apply, Measure.restrict_apply hA, smul_eq_mul]
  exact h _ inter_subset_right (hA.inter hU)

lemma kdNu_ge {m : Measure X} {f : E → X} {U : Set E} (hU : MeasurableSet U) (hf : ContinuousOn f U)
    (hinj : InjOn f U) (lam : Measure E) (d : ℝ≥0∞)
    (h : ∀ A ⊆ U, MeasurableSet A → d * lam A ≤ m (f '' A)) : d • lam.restrict U ≤ kdNu m f U := by
  refine Measure.le_iff.2 fun A hA => ?_
  rw [kdNu_apply hU hf hinj hA, Measure.smul_apply, Measure.restrict_apply hA, smul_eq_mul]
  exact h _ inter_subset_right (hA.inter hU)

end KDC

section KDC2

variable {E₁ E₂ X₁ X₂ : Type*} [TopologicalSpace E₁] [PolishSpace E₁] [MeasurableSpace E₁] [BorelSpace E₁]
  [TopologicalSpace E₂] [PolishSpace E₂] [MeasurableSpace E₂] [BorelSpace E₂]
  [TopologicalSpace X₁] [T2Space X₁] [MeasurableSpace X₁] [BorelSpace X₁] [SecondCountableTopology X₁]
  [TopologicalSpace X₂] [T2Space X₂] [MeasurableSpace X₂] [BorelSpace X₂] [SecondCountableTopology X₂]

lemma kdNu_prod {m₁ : Measure X₁} {m₂ : Measure X₂} [IsFiniteMeasure m₁] [IsFiniteMeasure m₂]
    {f₁ : E₁ → X₁} {f₂ : E₂ → X₂} {U₁ : Set E₁} {U₂ : Set E₂} (hU₁ : MeasurableSet U₁)
    (hU₂ : MeasurableSet U₂) (hf₁ : ContinuousOn f₁ U₁) (hf₂ : ContinuousOn f₂ U₂) (hi₁ : InjOn f₁ U₁)
    (hi₂ : InjOn f₂ U₂) :
    (kdNu m₁ f₁ U₁).prod (kdNu m₂ f₂ U₂) = kdNu (m₁.prod m₂) (Prod.map f₁ f₂) (U₁ ×ˢ U₂) := by
  have := kdNu_finite (m := m₁) hU₁ hf₁ hi₁
  have := kdNu_finite (m := m₂) hU₂ hf₂ hi₂
  refine Measure.prod_eq fun s t hs ht => ?_
  rw [kdNu_apply (hU₁.prod hU₂) (hf₁.prodMap hf₂) (hi₁.prodMap hi₂) (hs.prod ht),
    kdNu_apply hU₁ hf₁ hi₁ hs, kdNu_apply hU₂ hf₂ hi₂ ht, prod_inter_prod, prodMap_image_prod,
    Measure.prod_prod]

theorem kd_prod_bounds {m₁ : Measure X₁} {m₂ : Measure X₂} [IsFiniteMeasure m₁] [IsFiniteMeasure m₂]
    (lam₁ : Measure E₁) (lam₂ : Measure E₂) [SigmaFinite lam₁] [SigmaFinite lam₂]
    {f₁ : E₁ → X₁} {f₂ : E₂ → X₂} {U₁ : Set E₁} {U₂ : Set E₂} (hU₁ : MeasurableSet U₁)
    (hU₂ : MeasurableSet U₂) (hf₁ : ContinuousOn f₁ U₁) (hf₂ : ContinuousOn f₂ U₂) (hi₁ : InjOn f₁ U₁)
    (hi₂ : InjOn f₂ U₂) (c₁ d₁ c₂ d₂ : ℝ≥0∞)
    (h₁ : ∀ A ⊆ U₁, MeasurableSet A → m₁ (f₁ '' A) ≤ c₁ * lam₁ A ∧ d₁ * lam₁ A ≤ m₁ (f₁ '' A))
    (h₂ : ∀ A ⊆ U₂, MeasurableSet A → m₂ (f₂ '' A) ≤ c₂ * lam₂ A ∧ d₂ * lam₂ A ≤ m₂ (f₂ '' A))
    {B : Set (E₁ × E₂)} (hB : MeasurableSet B) (hBU : B ⊆ U₁ ×ˢ U₂) :
    (m₁.prod m₂) (Prod.map f₁ f₂ '' B) ≤ c₁ * c₂ * (lam₁.prod lam₂) B ∧
      d₁ * d₂ * (lam₁.prod lam₂) B ≤ (m₁.prod m₂) (Prod.map f₁ f₂ '' B) := by
  have := kdNu_finite (m := m₁) hU₁ hf₁ hi₁
  have := kdNu_finite (m := m₂) hU₂ hf₂ hi₂
  have e : (m₁.prod m₂) (Prod.map f₁ f₂ '' B) = ((kdNu m₁ f₁ U₁).prod (kdNu m₂ f₂ U₂)) B := by
    rw [kdNu_prod hU₁ hU₂ hf₁ hf₂ hi₁ hi₂,
      kdNu_apply (hU₁.prod hU₂) (hf₁.prodMap hf₂) (hi₁.prodMap hi₂) hB, inter_eq_left.2 hBU]
  have hs : ∀ a b : ℝ≥0∞,
      ((a • lam₁.restrict U₁).prod (b • lam₂.restrict U₂)) B = a * b * (lam₁.prod lam₂) B := by
    intro a b
    rw [Measure.prod_smul_left, Measure.prod_smul_right, Measure.prod_restrict, smul_smul,
      Measure.smul_apply, Measure.restrict_apply hB, inter_eq_left.2 hBU, smul_eq_mul]
  refine ⟨?_, ?_⟩
  · rw [e, ← hs c₁ c₂]
    exact Measure.le_iff'.1 (Measure.prod_mono
      (kdNu_le hU₁ hf₁ hi₁ lam₁ c₁ fun A hA hm => (h₁ A hA hm).1)
      (kdNu_le hU₂ hf₂ hi₂ lam₂ c₂ fun A hA hm => (h₂ A hA hm).1)) B
  · rw [e, ← hs d₁ d₂]
    exact Measure.le_iff'.1 (Measure.prod_mono
      (kdNu_ge hU₁ hf₁ hi₁ lam₁ d₁ fun A hA hm => (h₁ A hA hm).2)
      (kdNu_ge hU₂ hf₂ hi₂ lam₂ d₂ fun A hA hm => (h₂ A hA hm).2)) B

end KDC2

end ReciprocityTheory.ChartRestriction.DS
