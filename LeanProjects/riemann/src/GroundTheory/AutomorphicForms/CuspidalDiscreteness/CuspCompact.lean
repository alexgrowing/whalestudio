import Mathlib
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsLintegralConstantTermL2SqLe

open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain
open scoped ENNReal Pointwise NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace CuspidalSpectrum

open Reduction AutomorphicForm RightCosetSpace

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

local notation "Γ₁" => rationalGLOne K n

variable (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

instance completeSpace_cuspidalL2 : CompleteSpace (cuspidalL2 μ) :=
  (isClosed_cuspidalL2 μ).completeSpace_coe

def cuspRep : UnitaryRep (normOneGL K n) (cuspidalL2 μ) :=
  (rightRegularRep Γ₁ μ).restrict (cuspidalL2 μ) (isInvariant_cuspidalL2 μ)

theorem subtypeL_comp_integrated (f : (normOneGL K n) →₁[μ] ℂ) :
    (cuspidalL2 μ).subtypeL ∘L (cuspRep μ).integrated μ f =
      (rightRegularRep Γ₁ μ).integrated μ f ∘L (cuspidalL2 μ).subtypeL :=
  UnitaryRep.comp_integrated_of_mem_intertwiners (cuspRep μ) μ
    (UnitaryRep.subtypeL_mem_intertwiners _ _ _) f

theorem isCompactOperator_of_forall_norm_rconv_le
    (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ) (B : ℝ)
    (hB : ∀ φ ∈ cuspidalL2 μ, ∀ x, ‖rconv Γ₁ μ f φ x‖ ≤ B * ‖φ‖) :
    IsCompactOperator ((cuspRep μ).integrated μ (UnitaryRep.ccToL1 μ f)) := by
  have := isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  let T := (cuspRep μ).integrated μ (UnitaryRep.ccToL1 μ f)
  let T' : cuspidalL2 μ →L[ℂ] Lp ℂ 2 (quotientMeasure Γ₁ μ) := (cuspidalL2 μ).subtypeL ∘L T
  have hT' : T' = (rightRegularRep Γ₁ μ).integrated μ (UnitaryRep.ccToL1 μ f) ∘L
      (cuspidalL2 μ).subtypeL := subtypeL_comp_integrated μ _
  let e : RightCosetSpace Γ₁ → StrongDual ℂ (cuspidalL2 μ) := fun q =>
    (rconvCLM Γ₁ μ f (Quotient.out q)).comp (cuspidalL2 μ).subtypeL
  have he : ∀ q, ‖e q‖ ≤ max B 0 := by
    intro q
    refine ContinuousLinearMap.opNorm_le_bound _ (le_max_right _ _) fun v => ?_
    change ‖rconv Γ₁ μ f (v : Lp ℂ 2 (quotientMeasure Γ₁ μ)) (Quotient.out q)‖ ≤ _
    refine (hB v v.2 _).trans ?_
    rw [Submodule.coe_norm]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  have hout : ∀ (φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)) (q : RightCosetSpace Γ₁),
      rconvQ Γ₁ μ f φ q = rconv Γ₁ μ f φ (Quotient.out q) := by
    intro φ q
    obtain ⟨a, rfl⟩ := mk_surjective Γ₁ q
    obtain ⟨γ, hγ⟩ := (mk_eq_mk_iff (Γ := Γ₁)).1 (Quotient.out_eq (mk Γ₁ a))
    rw [rconvQ_mk, ← hγ]
    exact (rconv_mul_left Γ₁ μ f φ γ.2 a).symm
  have hae : ∀ v, T' v =ᵐ[quotientMeasure Γ₁ μ] fun q => e q v := by
    intro v
    have h1 : T' v = (rightRegularRep Γ₁ μ).integrated μ (UnitaryRep.ccToL1 μ f)
        (v : Lp ℂ 2 (quotientMeasure Γ₁ μ)) := by
      rw [hT']
      rfl
    rw [h1]
    filter_upwards [integrated_ae_eq_rconvQ Γ₁ μ f (v : Lp ℂ 2 (quotientMeasure Γ₁ μ))] with q hq
    exact hq.trans (hout _ q)
  have hHS : IsHilbertSchmidt T' := isHilbertSchmidt_of_ae_eq_dual T' e (max B 0) he hae
  have hc : IsCompactOperator T' := hHS.isCompactOperator
  have hmem : ∀ v, (fun v => T' v) v ∈ cuspidalL2 μ := fun v => (T v).2
  have hfun : (T : cuspidalL2 μ → cuspidalL2 μ) =
      Set.codRestrict (fun v => T' v) (cuspidalL2 μ) hmem :=
    funext fun v => Subtype.ext rfl
  rw [show ((cuspRep μ).integrated μ (UnitaryRep.ccToL1 μ f) : cuspidalL2 μ → cuspidalL2 μ) =
    (T : cuspidalL2 μ → cuspidalL2 μ) from rfl, hfun]
  exact hc.codRestrict hmem (isClosed_cuspidalL2 μ)

end CuspidalSpectrum

end

end GroundTheory.Automorphic
