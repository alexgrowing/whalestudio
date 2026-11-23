import Mathlib
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspCompact
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.DiscreteSpectrumAbstract

open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain
open scoped ENNReal Pointwise NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace UnitaryRep

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem dist_integrated_ccToL1_le (π : UnitaryRep G H) (ν : Measure G)
    [IsFiniteMeasureOnCompacts ν] (f f' : CompactlySupportedContinuousMap G ℂ) :
    dist (π.integrated ν (UnitaryRep.ccToL1 ν f)) (π.integrated ν (UnitaryRep.ccToL1 ν f')) ≤
      ∫ x, ‖f x - f' x‖ ∂ν := by
  have hf := f.continuous.memLp_of_hasCompactSupport (μ := ν) (p := 1) f.hasCompactSupport
  have hf' := f'.continuous.memLp_of_hasCompactSupport (μ := ν) (p := 1) f'.hasCompactSupport
  have h1 : UnitaryRep.ccToL1 ν f - UnitaryRep.ccToL1 ν f' = (hf.sub hf').toLp (⇑f - ⇑f') :=
    (MemLp.toLp_sub hf hf').symm
  have h2 : ‖UnitaryRep.ccToL1 ν f - UnitaryRep.ccToL1 ν f'‖ = ∫ x, ‖f x - f' x‖ ∂ν := by
    rw [h1, L1.norm_eq_integral_norm]
    exact integral_congr_ae ((hf.sub hf').coeFn_toLp.mono fun x hx => congrArg norm hx)
  calc dist (π.integrated ν (UnitaryRep.ccToL1 ν f)) (π.integrated ν (UnitaryRep.ccToL1 ν f'))
      = ‖π.integrated ν (UnitaryRep.ccToL1 ν f) - π.integrated ν (UnitaryRep.ccToL1 ν f')‖ :=
        dist_eq_norm _ _
    _ = ‖π.integrated ν (UnitaryRep.ccToL1 ν f - UnitaryRep.ccToL1 ν f')‖ := by
        rw [ContinuousLinearMap.map_sub]
    _ ≤ ‖UnitaryRep.ccToL1 ν f - UnitaryRep.ccToL1 ν f'‖ := π.norm_integrated_le ν _
    _ = ∫ x, ‖f x - f' x‖ ∂ν := h2

theorem isCompactOperator_integrated_of_approx (π : UnitaryRep G H) (ν : Measure G)
    [IsFiniteMeasureOnCompacts ν]
    (h : ∀ (f : CompactlySupportedContinuousMap G ℂ) (ε : ℝ), 0 < ε →
      ∃ f' : CompactlySupportedContinuousMap G ℂ,
        IsCompactOperator (π.integrated ν (UnitaryRep.ccToL1 ν f')) ∧ ∫ x, ‖f x - f' x‖ ∂ν ≤ ε)
    (f : CompactlySupportedContinuousMap G ℂ) :
    IsCompactOperator (π.integrated ν (UnitaryRep.ccToL1 ν f)) := by
  have hcl := isClosed_setOfPred_isCompactOperator (𝕜₁ := ℂ) (σ₁₂ := RingHom.id ℂ)
    (M₁ := H) (M₂ := H)
  have hmem : π.integrated ν (UnitaryRep.ccToL1 ν f) ∈
      closure {T : H →L[ℂ] H | IsCompactOperator T} := by
    refine Metric.mem_closure_iff.2 fun ε hε => ?_
    obtain ⟨f', hc, hf'⟩ := h f (ε / 2) (half_pos hε)
    exact ⟨_, hc, (π.dist_integrated_ccToL1_le ν f f').trans_lt
      (hf'.trans_lt (half_lt_self hε))⟩
  exact hcl.closure_subset hmem

end UnitaryRep

namespace CuspidalSpectrum

open Reduction AutomorphicForm RightCosetSpace

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

variable (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

include μ in

theorem exists_approx_bound (ν : Measure (ArchUnits K n)) [ν.IsHaarMeasure]
    (g : CompactlySupportedContinuousMap (normOneGL K n) ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ f' : CompactlySupportedContinuousMap (normOneGL K n) ℂ,
      (∃ B : ℝ, ∀ φ ∈ cuspidalL2 μ, ∀ x, ‖rconv (rationalGLOne K n) μ f' φ x‖ ≤ B * ‖φ‖) ∧
        ∫ x, ‖g x - f' x‖ ∂μ ≤ ε := by
  obtain ⟨U, hU, β, hβ, hβc, hβu, -, hclose⟩ := exists_smooth_approx μ ν g hε
  obtain ⟨B, hB⟩ := exists_norm_rconv_le_uniform μ ν hβ hβc hβu U hU g
  exact ⟨_, ⟨B, hB⟩,
    le_of_eq_of_le (integral_congr_ae (Eventually.of_forall fun x => norm_sub_rev _ _)) hclose⟩

theorem isCompactOperator_cuspRep (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ) :
    IsCompactOperator ((cuspRep μ).integrated μ (UnitaryRep.ccToL1 μ f)) :=
  Exists.elim (⟨Measure.haar, inferInstance⟩ : ∃ ν : Measure (ArchUnits K n), ν.IsHaarMeasure)
    fun ν hν => (cuspRep μ).isCompactOperator_integrated_of_approx μ (fun g _ hε =>
      (@exists_approx_bound K _ _ n μ _ ν hν g _ hε).imp fun f' hf' =>
        ⟨isCompactOperator_of_forall_norm_rconv_le μ f' hf'.1.choose hf'.1.choose_spec, hf'.2⟩) f

theorem exists_isHilbertSum_isIrreducible_cuspidal :
    ∃ s : Set (Submodule ℂ (cuspidalL2 μ)),
      ∃ _ : ∀ V : s, CompleteSpace (V : Submodule ℂ (cuspidalL2 μ)),
      ∃ hinv : ∀ V : s, (cuspRep μ).IsInvariant V,
      IsHilbertSum ℂ (fun V : s => (V : Submodule ℂ (cuspidalL2 μ)))
        (fun V => (V : Submodule ℂ (cuspidalL2 μ)).subtypeₗᵢ) ∧
      ∀ V : s, ((cuspRep μ).restrict V (hinv V)).IsIrreducible :=
  UnitaryRep.exists_isHilbertSum_isIrreducible (isCompactOperator_cuspRep μ)

end CuspidalSpectrum

end

end GroundTheory.Automorphic
