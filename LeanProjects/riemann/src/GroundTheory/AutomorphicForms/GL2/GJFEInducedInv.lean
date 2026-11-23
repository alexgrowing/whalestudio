import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJFEDefs

noncomputable section

namespace GroundTheory.Automorphic

namespace Measures

namespace LinearChart

open MeasureTheory Measure Set
open scoped NNReal ENNReal Pointwise

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] {ι : Type*} [Fintype ι]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  (C : LinearChart F ι G) (μ₀ : Measure (ι → F)) [μ₀.IsAddHaarMeasure]

theorem map_mul_right_haar_modular (h : G) :
    map (· * h) (C.haar μ₀) = modularCharacter h • C.haar μ₀ := by
  rw [C.map_mul_right_haar μ₀ h, C.modularCharacter_eq h]

include C in

theorem continuous_modularCharacter : Continuous (modularCharacter : G → ℝ≥0) := by
  have : (modularCharacter : G → ℝ≥0) = fun g => C.leftModulus g * (C.rightModulus g)⁻¹ := by
    funext g
    rw [C.modularCharacter_eq, div_eq_mul_inv]
  rw [this]
  exact C.continuous_leftModulus.mul
    (C.continuous_rightModulus.inv₀ fun g => (C.rightModulus_pos g).ne')

include C in
theorem measurable_modularCharacter :
    Measurable fun g : G => ((modularCharacter g : ℝ≥0) : ℝ≥0∞) :=
  (ENNReal.continuous_coe.comp (continuous_modularCharacter C)).measurable

theorem lintegral_mul_right_haar (h : G) {f : G → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f (x * h) ∂C.haar μ₀ = modularCharacter h * ∫⁻ x, f x ∂C.haar μ₀ := by
  rw [← lintegral_map hf (measurable_mul_const h), C.map_mul_right_haar_modular,
    lintegral_smul_measure]
  rfl

include C in

theorem modularCharacter_eq_one_of_mem {V : OpenSubgroup G} (hV : IsCompact (V : Set G)) {v : G}
    (hv : v ∈ V) : modularCharacter v = 1 := by
  obtain ⟨h1, h2⟩ := C.modulus_eq_one_of_mem hV hv
  rw [C.modularCharacter_eq, h1, h2, div_one]

variable [SecondCountableTopology G]

theorem map_inv_withDensity_haar :
    map (·⁻¹) ((C.haar μ₀).withDensity fun x => (modularCharacter x : ℝ≥0∞)) = C.haar μ₀ := by
  set μ := C.haar μ₀ with hμ
  set Δ : G → ℝ≥0∞ := fun x => (modularCharacter x : ℝ≥0∞) with hΔ
  have hΔm : Measurable Δ := (measurable_modularCharacter C)
  set ν := map (·⁻¹) (μ.withDensity Δ) with hνdef
  have hν : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂ν = ∫⁻ x, f x⁻¹ * Δ x ∂μ := by
    intro f hf
    rw [hνdef, lintegral_map hf measurable_inv]
    have := lintegral_withDensity_eq_lintegral_mul μ hΔm (hf.comp measurable_inv)
    simp only [Function.comp_def, Pi.mul_apply] at this
    rw [this]
    congr 1
    funext x
    ring

  have hleft : ∀ g : G, ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ x, f (g * x) ∂ν = ∫⁻ x, f x ∂ν := by
    intro g f hf
    rw [hν (fun x => f (g * x)) (hf.comp (measurable_const_mul g)), hν f hf]
    set L : G → ℝ≥0∞ := fun y => f y⁻¹ * Δ y with hLdef
    have hL : Measurable L := (hf.comp measurable_inv).mul hΔm
    have key : (fun x => f (g * x⁻¹) * Δ x) =
        fun x => (modularCharacter g : ℝ≥0∞) * L (x * g⁻¹) := by
      funext x
      have h1 : (x * g⁻¹)⁻¹ = g * x⁻¹ := by group
      have h2 : Δ x = (modularCharacter (x * g⁻¹) : ℝ≥0∞) * modularCharacter g := by
        rw [hΔ, ← ENNReal.coe_mul, ← map_mul, inv_mul_cancel_right]
      simp only [hLdef, h1, h2]
      ring
    show ∫⁻ x, f (g * x⁻¹) * Δ x ∂μ = ∫⁻ x, L x ∂μ
    rw [key, lintegral_const_mul (f := fun x => L (x * g⁻¹)) _ (hL.comp (measurable_mul_const _)),
      C.lintegral_mul_right_haar μ₀ g⁻¹ hL, ← mul_assoc, ← ENNReal.coe_mul, ← map_mul,
      mul_inv_cancel, map_one, ENNReal.coe_one, one_mul]
  have hinv : ν.IsMulLeftInvariant := ⟨fun g => by
    ext s hs
    rw [map_apply (measurable_const_mul g) hs, ← lintegral_indicator_one hs,
      ← lintegral_indicator_one (measurable_const_mul g hs)]
    exact hleft g (s.indicator 1) (measurable_one.indicator hs)⟩
  have hfin : IsFiniteMeasureOnCompacts ν := ⟨fun K hK => by
    rw [hνdef, map_apply measurable_inv hK.isClosed.measurableSet,
      withDensity_apply _ (measurable_inv hK.isClosed.measurableSet)]
    have hK' : IsCompact ((·⁻¹) ⁻¹' K : Set G) := by
      rw [Set.inv_preimage]
      exact hK.inv
    exact setLIntegral_lt_top_of_isCompact (hK'.measure_lt_top).ne hK'
      (continuous_modularCharacter C)⟩
  have hsmul := isMulLeftInvariant_eq_smul ν μ
  obtain ⟨V, hV⟩ := exists_compactOpenSubgroup (G := G)
  have hVm : MeasurableSet (V : Set G) := V.isOpen.measurableSet
  have hVinv : ((·⁻¹) ⁻¹' (V : Set G) : Set G) = V := by
    ext x
    simp
  have hνV : ν V = μ V := by
    rw [hνdef, map_apply measurable_inv hVm, withDensity_apply _ (measurable_inv hVm), hVinv]
    rw [setLIntegral_congr_fun hVm (g := fun _ => (1 : ℝ≥0∞)) fun x hx => by
      simp [hΔ, modularCharacter_eq_one_of_mem C hV hx]]
    simp
  have hμV0 : μ V ≠ 0 := V.isOpen.measure_ne_zero μ ⟨1, V.one_mem⟩
  have hμVt : μ V ≠ ∞ := hV.measure_lt_top.ne
  have hc : haarScalarFactor ν μ = 1 := by
    have := congrArg (fun m : Measure G => m V) hsmul
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at this
    rw [hνV] at this
    have h1 : (haarScalarFactor ν μ : ℝ≥0∞) * μ V = 1 * μ V := by rw [one_mul, ← this]
    exact_mod_cast (ENNReal.mul_left_inj hμV0 hμVt).1 h1
  rw [hsmul, hc, one_smul]

theorem lintegral_inv_haar {f : G → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x⁻¹ ∂C.haar μ₀ = ∫⁻ x, (modularCharacter x : ℝ≥0∞) * f x ∂C.haar μ₀ := by
  conv_lhs => rw [← C.map_inv_withDensity_haar μ₀]
  have h1 := lintegral_map (μ := (C.haar μ₀).withDensity fun x => (modularCharacter x : ℝ≥0∞))
    (f := fun x => f x⁻¹) (hf.comp measurable_inv) measurable_inv
  have h2 := lintegral_withDensity_eq_lintegral_mul (C.haar μ₀) (measurable_modularCharacter C) hf
  simp only [inv_inv] at h1
  rw [h1, h2]
  rfl

theorem integral_inv_haar {f : G → ℂ} (hf : Continuous f) :
    ∫ x, f x⁻¹ ∂C.haar μ₀ = ∫ x, (modularCharacter x : ℂ) * f x ∂C.haar μ₀ := by
  conv_lhs => rw [← C.map_inv_withDensity_haar μ₀]
  have h1 := integral_map (μ := (C.haar μ₀).withDensity fun x => (modularCharacter x : ℝ≥0∞))
    (φ := fun x : G => x⁻¹) (f := fun x => f x⁻¹) measurable_inv.aemeasurable
    (hf.comp continuous_inv).aestronglyMeasurable
  simp only [inv_inv] at h1
  rw [h1, integral_withDensity_eq_integral_smul (continuous_modularCharacter C).measurable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [NNReal.smul_def, Complex.real_smul]

end LinearChart

end Measures

end GroundTheory.Automorphic
