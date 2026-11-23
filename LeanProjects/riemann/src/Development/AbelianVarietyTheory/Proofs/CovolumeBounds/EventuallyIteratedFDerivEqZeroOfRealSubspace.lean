import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

open Metric Set Filter
open scoped Topology

namespace GlobalTheory.SCV

section General

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem fderiv_apply_eq_zero_of_frequently {f : E → V} {x s : E} (hf : DifferentiableAt ℂ f x)
    (h : ∃ᶠ t in 𝓝[≠] (0 : ℂ), f (x + t • s) = f x) : fderiv ℂ f x s = 0 := by
  have h1 : HasDerivAt (fun t : ℂ => f (x + t • s)) (fderiv ℂ f x s) 0 :=
    hf.hasFDerivAt.hasLineDerivAt s
  rw [hasDerivAt_iff_tendsto_slope_zero] at h1
  refine tendsto_nhds_unique_of_frequently_eq h1 tendsto_const_nhds (h.mono fun t ht => ?_)
  simp [ht]

theorem frequently_nhdsNE_of_eventually_ofReal {p : ℂ → Prop}
    (h : ∀ᶠ t : ℝ in 𝓝 0, p t) : ∃ᶠ t in 𝓝[≠] (0 : ℂ), p t := by
  have h1 : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact (Complex.continuous_ofReal.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simpa using ht
  exact h1.frequently (h.filter_mono nhdsWithin_le_nhds).frequently

theorem fderiv_eq_zero_of_real_lines {f : E → V} {x : E} {S : Set E}
    (hS : Submodule.span ℂ S = ⊤) (hf : DifferentiableAt ℂ f x)
    (h : ∀ s ∈ S, ∀ᶠ t : ℝ in 𝓝 0, f (x + (t : ℂ) • s) = f x) : fderiv ℂ f x = 0 := by
  have : (fderiv ℂ f x : E →ₗ[ℂ] V) = 0 :=
    LinearMap.ext_on hS fun s hs => fderiv_apply_eq_zero_of_frequently hf
      (frequently_nhdsNE_of_eventually_ofReal (p := fun t => f (x + t • s) = f x) (h s hs))
  ext v
  exact LinearMap.congr_fun this v

theorem eq_of_eventually_real_lines {f : E → V} {U S : Set E}
    (hS : Submodule.span ℂ S = ⊤) (hU : IsOpen U) (hU' : IsPreconnected U)
    (hf : DifferentiableOn ℂ f U)
    (h : ∀ z ∈ U, ∀ s ∈ S, ∀ᶠ t : ℝ in 𝓝 0, f (z + (t : ℂ) • s) = f z)
    {z w : E} (hz : z ∈ U) (hw : w ∈ U) : f z = f w :=
  hU.is_const_of_fderiv_eq_zero hU' hf
    (fun x hx => fderiv_eq_zero_of_real_lines hS (hf.differentiableAt (hU.mem_nhds hx)) (h x hx))
    hz hw

theorem eq_of_invariant_real_lines {f : E → V} {U S : Set E}
    (hS : Submodule.span ℂ S = ⊤) (hU : IsOpen U) (hU' : IsPreconnected U)
    (hf : DifferentiableOn ℂ f U)
    (h : ∀ z ∈ U, ∀ s ∈ S, ∀ t : ℝ, z + (t : ℂ) • s ∈ U → f (z + (t : ℂ) • s) = f z)
    {z w : E} (hz : z ∈ U) (hw : w ∈ U) : f z = f w := by
  refine eq_of_eventually_real_lines hS hU hU' hf (fun x hx s hs => ?_) hz hw
  have h1 : Tendsto (fun t : ℝ => x + (t : ℂ) • s) (𝓝 0) (𝓝 x) :=
    Continuous.tendsto' (by fun_prop) _ _ (by simp)
  exact (h1.eventually (hU.mem_nhds hx)).mono fun t ht => h x hx s hs t ht

variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

theorem eq_of_invariant_realSubspace {f : E → V} {U : Set E} {S : Submodule ℝ E}
    (hS : Submodule.span ℂ (S : Set E) = ⊤) (hU : IsOpen U) (hU' : IsPreconnected U)
    (hf : DifferentiableOn ℂ f U) (h : ∀ z ∈ U, ∀ s ∈ S, z + s ∈ U → f (z + s) = f z)
    {z w : E} (hz : z ∈ U) (hw : w ∈ U) : f z = f w := by
  refine eq_of_invariant_real_lines hS hU hU' hf (fun x hx s hs t ht => h x hx _ ?_ ht) hz hw
  rw [show (t : ℂ) • s = t • s from algebraMap_smul ℂ t s]
  exact S.smul_mem t hs

variable [FiniteDimensional ℂ E] [CompleteSpace V]

end General

section Coordinates

variable {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℂ V]

noncomputable def scaledRealPoints (ι : Type*) (a : ℂ) : Submodule ℝ (ι → ℂ) where
  carrier := {z | ∃ x : ι → ℝ, z = fun i => a * x i}
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, by ext i; simp [mul_add]⟩
  zero_mem' := ⟨0, by ext i; simp⟩
  smul_mem' := by
    rintro t _ ⟨x, rfl⟩
    exact ⟨t • x, by ext i; simp [mul_left_comm]⟩

omit [Fintype ι] in

theorem span_scaledRealPoints {a : ℂ} (ha : a ≠ 0) :
    Submodule.span ℂ (scaledRealPoints ι a : Set (ι → ℂ)) = ⊤ := by
  refine eq_top_iff.mpr fun z _ => ?_
  have e : z = a⁻¹ • (fun i => a * ((z i).re : ℂ))
      + (a⁻¹ * Complex.I) • (fun i => a * ((z i).im : ℂ)) := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← Complex.re_add_im (z i)]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im,
      Complex.mul_im, zero_add]
    field_simp
  rw [e]
  exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))

theorem eq_of_invariant_real {f : (ι → ℂ) → V} {U : Set (ι → ℂ)}
    (hU : IsOpen U) (hU' : IsPreconnected U) (hf : DifferentiableOn ℂ f U)
    (h : ∀ z ∈ U, ∀ x : ι → ℝ, (z + fun i => (x i : ℂ)) ∈ U → f (z + fun i => (x i : ℂ)) = f z)
    {z w : ι → ℂ} (hz : z ∈ U) (hw : w ∈ U) : f z = f w := by
  refine eq_of_invariant_realSubspace (span_scaledRealPoints one_ne_zero) hU hU' hf ?_ hz hw
  rintro y hy _ ⟨x, rfl⟩
  simpa only [one_mul] using h y hy x

variable [CompleteSpace V]

end Coordinates

end GlobalTheory.SCV
