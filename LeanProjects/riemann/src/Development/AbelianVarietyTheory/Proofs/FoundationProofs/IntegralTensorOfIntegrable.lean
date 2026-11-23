import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset

open MeasureTheory Set Filter GlobalTheory.AdelicU GlobalTheory.SplitWeil NumberField IsDedekindDomain
open GlobalTheory.AutomorphicL2Unitary (conv)

noncomputable section

namespace GlobalTheory.Orb

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
  [Submodule.IsLattice E L] {μa : ∀ w, Measure (GArch σ J w)} {μf : ∀ v, Measure (GLoc σ J v)}
  {μ : Measure (GAd σ J)} {fa fa' : ∀ w, GArch σ J w → ℂ} {ff ff' : ∀ v, GLoc σ J v → ℂ}

omit [Submodule.IsLattice E L] in

theorem unitLoc_mul_translate {v : HeightOneSpectrum (𝓞 F)} {y : GLoc σ J v} (hy : y ∈ stabLoc σ J L v) :
    (fun x => unitLoc σ J L v x * unitLoc σ J L v (x⁻¹ * y)) = unitLoc σ J L v := by
  funext x
  by_cases hx : x ∈ stabLoc σ J L v
  · simp [unitLoc, hx, mul_mem (inv_mem hx) hy]
  · simp [unitLoc, hx]

theorem conv_unitLoc {v : HeightOneSpectrum (𝓞 F)} (ν : Measure (GLoc σ J v)) :
    conv ν (unitLoc σ J L v) (unitLoc σ J L v) = (ν.real (stabLoc σ J L v) : ℂ) • unitLoc σ J L v := by
  funext y
  by_cases hy : y ∈ stabLoc σ J L v
  · rw [conv, unitLoc_mul_translate hy, unitLoc]
    refine (integral_indicator_const _ (isOpen_stabLoc σ J L v).measurableSet).trans ?_
    rw [Pi.smul_apply, indicator_of_mem hy, Complex.real_smul]
    rfl
  · have : ∀ x, unitLoc σ J L v x * unitLoc σ J L v (x⁻¹ * y) = 0 := fun x => by
      by_cases hx : x ∈ stabLoc σ J L v
      · simp [unitLoc, hy, Subgroup.mul_mem_cancel_left _ (inv_mem hx)]
      · simp [unitLoc, hx]
    rw [conv]
    simp only [this, integral_zero]
    simp [unitLoc, hy]

theorem IsFinFamily.conv (hf : IsFinFamily σ J L ff) (hf' : IsFinFamily σ J L ff')
    (h1 : ∀ᶠ v in cofinite, μf v (stabLoc σ J L v) = 1) : IsFinFamily σ J L fun v => conv (μf v) (ff v) (ff' v) := by
  refine ⟨fun v => conv_mem_SB (hf.1 v) (hf'.1 v), ?_⟩
  filter_upwards [hf.2, hf'.2, h1] with v e e' e1
  rw [e, e', conv_unitLoc, Measure.real, e1]
  simp

theorem IsFinFamily.mul_translate (hf : IsFinFamily σ J L ff) (hf' : IsFinFamily σ J L ff') (y : GAd σ J) :
    IsFinFamily σ J L fun v x => ff v x * ff' v (x⁻¹ * proj σ J v y) := by
  refine ⟨fun v => ⟨(hf.1 v).1.mul ((hf'.1 v).1.comp_continuous (by fun_prop)), (hf.1 v).2.mul_right⟩, ?_⟩
  filter_upwards [hf.2, hf'.2, eventually_proj_mem_stabLoc σ J L y] with v e e' hy
  rw [e, e', unitLoc_mul_translate hy]

theorem integral_tensor_of_integrable (hμ : IsRestrictedProd σ J L μa μf μ) (ha : ∀ w, Integrable (fa w) (μa w))
    (hf : IsFinFamily σ J L ff) :
    Integrable (tensor σ J fa ff) μ ∧
      ∫ g, tensor σ J fa ff g ∂μ = (∏ w, ∫ y, fa w y ∂μa w) * ∏ᶠ v, ∫ y, ff v y ∂μf v := by
  have := hμ.haar_loc
  let S := (eventually_cofinite.1 (hf.2.and hμ.eventually_eq_one)).toFinset
  have hS : ∀ v ∉ S, ff v = unitLoc σ J L v ∧ μf v (stabLoc σ J L v) = 1 := fun v hv => by
    simpa only [S, Finite.mem_toFinset, mem_setOf_eq, not_not] using hv
  rw [finprod_eq_prod_of_mulSupport_subset (s := S) _ fun v hv => by_contra fun h => hv (by
    rw [(hS v h).1, unitLoc]
    refine (integral_indicator_const _ (isOpen_stabLoc σ J L v).measurableSet).trans ?_
    rw [Measure.real, (hS v h).2, ENNReal.toReal_one, one_smul]; rfl)]
  exact ((hμ.euler_product S fun v hv => (hS v hv).2).1 fa ff ha).2.1
    (fun v hv => (hS v hv).1) fun v _ => (hf.1 v).1.continuous.integrable_of_hasCompactSupport (hf.1 v).2

theorem tensor_mul_translate (hf : IsFinFamily σ J L ff) (hf' : IsFinFamily σ J L ff') (y : GAd σ J) :
    (fun x => tensor σ J fa ff x * tensor σ J fa' ff' (x⁻¹ * y)) =
      tensor σ J (fun w x => fa w x * fa' w (x⁻¹ * projArch σ J w y))
        fun v x => ff v x * ff' v (x⁻¹ * proj σ J v y) := by
  funext x
  have h1 := hf.finite_mulSupport (projFin σ J x)
  have h2 := hf'.finite_mulSupport (projFin σ J (x⁻¹ * y))
  simp only [projFinLoc_projFin] at h1 h2
  simp only [map_mul, map_inv] at h2
  simp only [tensor, map_mul, map_inv]
  rw [finprod_mul_distrib h1 h2, Finset.prod_mul_distrib, mul_mul_mul_comm]

theorem conv_tensor_of_continuous (hμ : IsRestrictedProd σ J L μa μf μ) (ha : ∀ w, Continuous (fa w))
    (hc : ∀ w, HasCompactSupport (fa w)) (ha' : ∀ w, Continuous (fa' w))
    (hf : IsFinFamily σ J L ff) (hf' : IsFinFamily σ J L ff') :
    (∀ y, Integrable (fun x => tensor σ J fa ff x * tensor σ J fa' ff' (x⁻¹ * y)) μ) ∧
      IsFinFamily σ J L (fun v => conv (μf v) (ff v) (ff' v)) ∧
      conv μ (tensor σ J fa ff) (tensor σ J fa' ff') =
        tensor σ J (fun w => conv (μa w) (fa w) (fa' w)) fun v => conv (μf v) (ff v) (ff' v) := by
  have := hμ.haar_arch
  have key := fun y => integral_tensor_of_integrable hμ
    (fa := fun w x => fa w x * fa' w (x⁻¹ * projArch σ J w y))
    (fun w => ((ha w).mul ((ha' w).comp (by fun_prop))).integrable_of_hasCompactSupport (hc w).mul_right)
    (hf.mul_translate hf' y)
  refine ⟨fun y => ?_, hf.conv hf' hμ.eventually_eq_one, funext fun y => ?_⟩
  · rw [tensor_mul_translate hf hf']
    exact (key y).1
  · rw [conv, tensor_mul_translate hf hf', (key y).2]
    rfl

theorem conv_tensor (hμ : IsRestrictedProd σ J L μa μf μ) (ha : ∀ w, fa w ∈ CcArch σ J w)
    (ha' : ∀ w, fa' w ∈ CcArch σ J w) (hf : IsFinFamily σ J L ff) (hf' : IsFinFamily σ J L ff') :
    IsFinFamily σ J L (fun v => conv (μf v) (ff v) (ff' v)) ∧
      conv μ (tensor σ J fa ff) (tensor σ J fa' ff') =
        tensor σ J (fun w => conv (μa w) (fa w) (fa' w)) fun v => conv (μf v) (ff v) (ff' v) :=
  (conv_tensor_of_continuous hμ (fun w => continuous_of_mem_ccSmooth (continuous_archCoord σ J w) (ha w))
    (fun w => (ha w).1) (fun w => continuous_of_mem_ccSmooth (continuous_archCoord σ J w) (ha' w)) hf hf').2

end GlobalTheory.Orb
