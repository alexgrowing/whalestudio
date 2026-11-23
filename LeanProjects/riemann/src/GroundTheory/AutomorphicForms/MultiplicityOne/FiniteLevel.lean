import Mathlib
import GroundTheory.AutomorphicForms.MultiplicityOne.ContinuousWhittakerOneRconvIntertwiner
import GroundTheory.AutomorphicForms.UnitaryRepresentations.ExistsEqAlgebraMapOfIsSelfAdjoint

open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain
open scoped ENNReal Pointwise NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace MultiplicityOne

open Reduction AutomorphicForm RightCosetSpace CuspidalSpectrum FourierWhittaker

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

local notation "Γ₁" => rationalGLOne K n

variable {μ : Measure (normOneGL K n)} [μ.IsHaarMeasure]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {σ : UnitaryRep (normOneGL K n) H}

set_option maxHeartbeats 2000000 in

theorem isCompactOperator_integrated_comp_of_bound (T : cuspIntertwiners μ σ)
    (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ) (B : ℝ)
    (hB : ∀ φ ∈ cuspidalL2 μ, ∀ x, ‖rconv Γ₁ μ f φ x‖ ≤ B * ‖φ‖) :
    IsCompactOperator ((rightRegularRep Γ₁ μ).integrated μ (UnitaryRep.ccToL1 μ f) ∘L T.1) := by
  have := isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  let e : RightCosetSpace Γ₁ → StrongDual ℂ H := fun q =>
    (rconvCLM Γ₁ μ f (Quotient.out q)).comp T.1
  have he : ∀ q, ‖e q‖ ≤ max B 0 * ‖T.1‖ := by
    intro q
    refine ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (le_max_right _ _) (norm_nonneg _)) fun v => ?_
    change ‖rconv Γ₁ μ f (T.1 v) (Quotient.out q)‖ ≤ _
    refine (hB _ (T.2.2 v) _).trans ?_
    rw [mul_assoc]
    refine mul_le_mul (le_max_left _ _) (T.1.le_opNorm v) (norm_nonneg _) (le_max_right _ _)
  have hout : ∀ (φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)) (q : RightCosetSpace Γ₁),
      rconvQ Γ₁ μ f φ q = rconv Γ₁ μ f φ (Quotient.out q) := by
    intro φ q
    obtain ⟨a, rfl⟩ := mk_surjective Γ₁ q
    obtain ⟨γ, hγ⟩ := (mk_eq_mk_iff (Γ := Γ₁)).1 (Quotient.out_eq (mk Γ₁ a))
    rw [rconvQ_mk, ← hγ]
    exact (rconv_mul_left Γ₁ μ f φ γ.2 a).symm
  have hae : ∀ v, ((rightRegularRep Γ₁ μ).integrated μ (UnitaryRep.ccToL1 μ f) ∘L T.1) v =ᵐ[quotientMeasure Γ₁ μ]
      fun q => e q v := by
    intro v
    filter_upwards [integrated_ae_eq_rconvQ Γ₁ μ f (T.1 v)] with q hq
    exact hq.trans (hout _ q)
  exact (isHilbertSchmidt_of_ae_eq_dual _ e _ he hae).isCompactOperator

omit [NumberField K] [μ.IsHaarMeasure] [CompleteSpace H] in
theorem exists_pos_mul_add_one_lt {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) :
    ∃ ε' : ℝ, 0 < ε' ∧ ε' * (a + 1) < ε := by
  refine ⟨ε / (2 * (a + 1)), div_pos hε (by positivity), ?_⟩
  have h : ε / (2 * (a + 1)) * (a + 1) = ε / 2 := by field_simp
  rw [h]
  linarith

set_option maxHeartbeats 8000000 in

theorem isCompactOperator_integrated_comp (T : cuspIntertwiners μ σ)
    (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ) :
    IsCompactOperator ((rightRegularRep Γ₁ μ).integrated μ (UnitaryRep.ccToL1 μ f) ∘L T.1) := by
  have hcl := isClosed_setOfPred_isCompactOperator (𝕜₁ := ℂ) (σ₁₂ := RingHom.id ℂ)
    (M₁ := H) (M₂ := Lp ℂ 2 (quotientMeasure Γ₁ μ))
  refine hcl.closure_subset (Metric.mem_closure_iff.2 fun ε hε => ?_)
  obtain ⟨ε', hε', hεε⟩ := exists_pos_mul_add_one_lt (norm_nonneg T.1) hε
  obtain ⟨f', ⟨B, hB⟩, hff'⟩ :=
    exists_approx_bound μ (Measure.haar : Measure (ArchUnits K n)) f hε'
  refine ⟨_, isCompactOperator_integrated_comp_of_bound T f' B hB, ?_⟩
  rw [dist_eq_norm, ← ContinuousLinearMap.sub_comp]
  calc ‖((rightRegularRep Γ₁ μ).integrated μ (UnitaryRep.ccToL1 μ f) -
        (rightRegularRep Γ₁ μ).integrated μ (UnitaryRep.ccToL1 μ f')) ∘L T.1‖
      ≤ ‖(rightRegularRep Γ₁ μ).integrated μ (UnitaryRep.ccToL1 μ f) -
        (rightRegularRep Γ₁ μ).integrated μ (UnitaryRep.ccToL1 μ f')‖ * ‖T.1‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ε' * (‖T.1‖ + 1) := by
        refine mul_le_mul ?_ (le_add_of_nonneg_right zero_le_one) (norm_nonneg _) hε'.le
        rw [← dist_eq_norm]
        exact ((rightRegularRep Γ₁ μ).dist_integrated_ccToL1_le μ f f').trans hff'
    _ < ε := hεε

set_option maxHeartbeats 4000000 in

theorem isCompactOperator_integrated_of_irreducible (hσ : σ.IsIrreducible)
    (T : cuspIntertwiners μ σ) (hT0 : T ≠ 0)
    (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ) :
    IsCompactOperator (σ.integrated μ (UnitaryRep.ccToL1 μ f)) := by
  obtain ⟨c, hc⟩ := hσ.exists_eq_smul_one (UnitaryRep.comp_mem_intertwiners
    (UnitaryRep.adjoint_mem_intertwiners T.2.1) T.2.1)
  have hT0' : T.1 ≠ 0 := fun h => hT0 (Subtype.ext h)
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hT0'
    refine ContinuousLinearMap.ext fun k => ?_
    have h := congrArg (fun A : H →L[ℂ] H => inner ℂ k (A k)) hc
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right, zero_smul] at h
    simpa using h
  have hint := UnitaryRep.comp_integrated_of_mem_intertwiners σ μ T.2.1 (UnitaryRep.ccToL1 μ f)
  have e : ContinuousLinearMap.adjoint T.1 ∘L
      ((rightRegularRep Γ₁ μ).integrated μ (UnitaryRep.ccToL1 μ f) ∘L T.1) =
      c • σ.integrated μ (UnitaryRep.ccToL1 μ f) := by
    rw [← hint, ← ContinuousLinearMap.comp_assoc, hc, ContinuousLinearMap.smul_comp,
      ← ContinuousLinearMap.mul_def, one_mul]
  have e2 : σ.integrated μ (UnitaryRep.ccToL1 μ f) = c⁻¹ • (ContinuousLinearMap.adjoint T.1 ∘L
      ((rightRegularRep Γ₁ μ).integrated μ (UnitaryRep.ccToL1 μ f) ∘L T.1)) := by
    rw [e, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [e2, FunLike.coe_smul, ContinuousLinearMap.coe_comp]
  exact ((isCompactOperator_integrated_comp T f).clm_comp (ContinuousLinearMap.adjoint T.1)).smul c⁻¹

end MultiplicityOne

end

end GroundTheory.Automorphic
