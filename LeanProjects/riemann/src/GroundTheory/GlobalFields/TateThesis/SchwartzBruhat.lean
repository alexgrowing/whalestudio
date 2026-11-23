import Mathlib
import GroundTheory.GlobalFields.TateThesis.SchwartzBruhatFinite
import GroundTheory.GlobalFields.TateThesis.AdeleScaling

namespace GroundTheory.Global

open NumberField NumberField.mixedEmbedding IsDedekindDomain MeasureTheory Measure Filter
open scoped NumberField.AdeleRing ENNReal NNReal SchwartzMap FourierTransform Real Classical

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem infiniteTrace_mul (x y : InfiniteAdeleRing K) :
    infiniteTrace K (x * y) =
      mixedTraceForm K (homeomorphMixedSpace K x) (homeomorphMixedSpace K y) := by
  rw [← mixedTrace_homeomorphMixedSpace, homeomorphMixedSpace_mul, mixedTraceForm_apply]

theorem adelicChar_mul_eq (x y : 𝔸[K]) :
    (adelicChar K (x * y) : ℂ) =
      (𝐞 (-mixedTraceForm K (homeomorphMixedSpace K x.1) (homeomorphMixedSpace K y.1)) : ℂ) *
        (finiteAdelicChar K (x.2 * y.2) : ℂ) := by
  have hxy : x * y = infiniteAdeleInl (x.1 * y.1) + finiteAdeleInr (x.2 * y.2) :=
    (infiniteAdeleInl_add_finiteAdeleInr (x * y)).symm
  have hinf : adelicChar K (infiniteAdeleInl (x.1 * y.1)) = 𝐞 (-infiniteTrace K (x.1 * y.1)) :=
    adelicChar_infinite _
  rw [hxy, AddChar.map_add_eq_mul, Circle.coe_mul, hinf, infiniteTrace_mul, finiteAdelicChar_apply]

def schwartzBruhatTensor (φ : 𝓢(mixedSpace K, ℂ)) (g : 𝔸ᶠ[K] → ℂ) : 𝔸[K] → ℂ :=
  fun x ↦ φ (homeomorphMixedSpace K x.1) * g x.2

variable (K) in

def schwartzBruhat : Submodule ℂ (𝔸[K] → ℂ) :=
  Submodule.span ℂ {F | ∃ φ : 𝓢(mixedSpace K, ℂ), ∃ g ∈ finiteSchwartzBruhat K,
    F = schwartzBruhatTensor φ g}

theorem schwartzBruhatTensor_mem (φ : 𝓢(mixedSpace K, ℂ)) {g : 𝔸ᶠ[K] → ℂ}
    (hg : g ∈ finiteSchwartzBruhat K) : schwartzBruhatTensor φ g ∈ schwartzBruhat K :=
  Submodule.subset_span ⟨φ, g, hg, rfl⟩

theorem integrable_schwartz_comp (φ : 𝓢(mixedSpace K, ℂ)) :
    Integrable (fun z ↦ φ (homeomorphMixedSpace K z)) (infiniteAdeleMeasure K) :=
  ((measurePreserving_measurableEquivMixedSpace K).integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _)).mpr (φ.integrable (μ := selfDualMeasure K))

theorem integrable_schwartzBruhatTensor (φ : 𝓢(mixedSpace K, ℂ)) {g : 𝔸ᶠ[K] → ℂ}
    (hg : g ∈ finiteSchwartzBruhat K) :
    Integrable (schwartzBruhatTensor φ g) (adeleMeasure K) :=
  (integrable_schwartz_comp φ).mul_prod (integrable_of_mem_finiteSchwartzBruhat hg)

theorem integrable_of_mem_schwartzBruhat {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K) :
    Integrable F (adeleMeasure K) := by
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    exact integrable_schwartzBruhatTensor φ hg
  | zero => exact integrable_zero _ _ _
  | add G H _ _ hG hH => exact hG.add hH
  | smul c G _ hG => exact hG.smul c

variable (K) in

def adelicFourier (F : 𝔸[K] → ℂ) (y : 𝔸[K]) : ℂ :=
  ∫ x, F x * (adelicChar K (x * y) : ℂ) ∂adeleMeasure K

theorem continuous_adelicChar_mul_const (y : 𝔸[K]) :
    Continuous fun x : 𝔸[K] ↦ (adelicChar K (x * y) : ℂ) :=
  continuous_subtype_val.comp ((continuous_adelicChar (K := K)).comp (continuous_mul_const y))

theorem integrable_mul_adelicChar {F : 𝔸[K] → ℂ} (hF : Integrable F (adeleMeasure K))
    (y : 𝔸[K]) :
    Integrable (fun x ↦ F x * (adelicChar K (x * y) : ℂ)) (adeleMeasure K) :=
  hF.mono (hF.1.mul (continuous_adelicChar_mul_const y).aestronglyMeasurable)
    (Eventually.of_forall fun x ↦ by rw [norm_mul, Circle.norm_coe, mul_one])

theorem adelicFourier_add {F G : 𝔸[K] → ℂ} (hF : Integrable F (adeleMeasure K))
    (hG : Integrable G (adeleMeasure K)) :
    adelicFourier K (F + G) = adelicFourier K F + adelicFourier K G := by
  funext y
  simp only [adelicFourier, Pi.add_apply, add_mul]
  exact integral_add (integrable_mul_adelicChar hF y) (integrable_mul_adelicChar hG y)

theorem adelicFourier_smul (c : ℂ) (F : 𝔸[K] → ℂ) :
    adelicFourier K (c • F) = c • adelicFourier K F := by
  funext y
  simp only [adelicFourier, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul c _

theorem adelicFourier_zero : adelicFourier K (0 : 𝔸[K] → ℂ) = 0 := by
  funext y
  simp [adelicFourier]

theorem integral_infinite_eq_mixedFourier (φ : 𝓢(mixedSpace K, ℂ)) (y : InfiniteAdeleRing K) :
    ∫ z, φ (homeomorphMixedSpace K z) *
        (𝐞 (-mixedTraceForm K (homeomorphMixedSpace K z) (homeomorphMixedSpace K y)) : ℂ)
        ∂infiniteAdeleMeasure K =
      mixedFourier K φ (homeomorphMixedSpace K y) := by
  rw [mixedFourier_apply]
  have h := (measurePreserving_measurableEquivMixedSpace K).integral_comp'
    (fun m ↦ 𝐞 (-mixedTraceForm K m (homeomorphMixedSpace K y)) • φ m)
  refine Eq.trans ?_ h
  refine integral_congr_ae (Eventually.of_forall fun z ↦ ?_)
  simp only [measurableEquivMixedSpace_apply, Circle.smul_def, smul_eq_mul]
  ring

theorem adelicFourier_schwartzBruhatTensor (φ : 𝓢(mixedSpace K, ℂ)) (g : 𝔸ᶠ[K] → ℂ) :
    adelicFourier K (schwartzBruhatTensor φ g) =
      schwartzBruhatTensor (mixedFourierSchwartz K φ) (finiteFourier K g) := by
  funext y
  have h := integral_prod_mul (μ := infiniteAdeleMeasure K) (ν := finiteAdeleMeasure K)
    (fun z ↦ φ (homeomorphMixedSpace K z) *
      (𝐞 (-mixedTraceForm K (homeomorphMixedSpace K z) (homeomorphMixedSpace K y.1)) : ℂ))
    (fun z ↦ g z * (finiteAdelicChar K (z * y.2) : ℂ))
  rw [integral_infinite_eq_mixedFourier] at h
  rw [schwartzBruhatTensor, mixedFourierSchwartz_apply, finiteFourier, ← h, adelicFourier]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only [schwartzBruhatTensor, adelicChar_mul_eq]
  ring

theorem adelicFourier_mem_schwartzBruhat {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K) :
    adelicFourier K F ∈ schwartzBruhat K := by
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    rw [adelicFourier_schwartzBruhatTensor]
    exact schwartzBruhatTensor_mem _ (finiteFourier_mem_finiteSchwartzBruhat hg)
  | zero => rw [adelicFourier_zero]; exact zero_mem _
  | add G H hG hH ihG ihH =>
    rw [adelicFourier_add (integrable_of_mem_schwartzBruhat hG)
      (integrable_of_mem_schwartzBruhat hH)]
    exact add_mem ihG ihH
  | smul c G _ ih =>
    rw [adelicFourier_smul]
    exact Submodule.smul_mem _ c ih

theorem mixedFourier_neg (f : mixedSpace K → ℂ) (m : mixedSpace K) :
    mixedFourier K f (-m) = mixedFourierInv K f m := by
  rw [mixedFourier_apply, mixedFourierInv_apply]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only [map_neg, neg_neg, mixedTraceForm_comm K x m]

theorem mixedFourier_mixedFourier (φ : 𝓢(mixedSpace K, ℂ)) (m : mixedSpace K) :
    mixedFourier K (mixedFourier K φ) m = φ (-m) := by
  rw [← neg_neg m, mixedFourier_neg, mixedFourierInv_mixedFourier, neg_neg]

theorem adelicFourier_adelicFourier {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K) :
    adelicFourier K (adelicFourier K F) = fun x ↦ F (-x) := by
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    rw [adelicFourier_schwartzBruhatTensor, adelicFourier_schwartzBruhatTensor,
      finiteFourier_finiteFourier hg]
    funext x
    simp only [schwartzBruhatTensor, mixedFourierSchwartz_apply]
    rw [mixedFourier_mixedFourier]
    congr 2
    show -homeomorphMixedSpace K x.1 = homeomorphMixedSpace K (-x.1)
    rw [homeomorphMixedSpace_apply, homeomorphMixedSpace_apply, map_neg]
  | zero => funext x; simp [adelicFourier_zero]
  | add G H hG hH ihG ihH =>
    rw [adelicFourier_add (integrable_of_mem_schwartzBruhat hG)
        (integrable_of_mem_schwartzBruhat hH),
      adelicFourier_add (integrable_of_mem_schwartzBruhat (adelicFourier_mem_schwartzBruhat hG))
        (integrable_of_mem_schwartzBruhat (adelicFourier_mem_schwartzBruhat hH)), ihG, ihH]
    rfl
  | smul c G _ ih =>
    rw [adelicFourier_smul, adelicFourier_smul, ih]
    rfl

theorem adelicFourier_comp_smul (a : IdeleGroup K) (F : 𝔸[K] → ℂ) (y : 𝔸[K]) :
    adelicFourier K (fun x ↦ F (a • x)) y =
      ((IdeleGroup.ideleModule K a : ℝ)⁻¹ : ℂ) * adelicFourier K F (a⁻¹ • y) := by
  set G : 𝔸[K] → ℂ := fun z ↦ F z * (adelicChar K (z * (a⁻¹ • y)) : ℂ)
  have hG : ∀ x, G (a • x) = F (a • x) * (adelicChar K (x * y) : ℂ) := by
    intro x
    simp only [G]
    rw [Units.smul_def, Units.smul_def, smul_eq_mul, smul_eq_mul, mul_mul_mul_comm, Units.mul_inv,
      one_mul]
  have hemb : MeasurableEmbedding fun x : 𝔸[K] ↦ a • x :=
    (Homeomorph.smul a).toMeasurableEquiv.measurableEmbedding
  have h := hemb.integral_map (μ := adeleMeasure K) G
  rw [map_smul_adeleMeasure, integral_smul_measure, ENNReal.toReal_ofReal
    (inv_nonneg.mpr (IdeleGroup.ideleModule K a).2.le)] at h
  rw [adelicFourier, adelicFourier]
  simp only [← hG]
  rw [← h, Complex.real_smul, Complex.ofReal_inv]

end

end GroundTheory.Global
