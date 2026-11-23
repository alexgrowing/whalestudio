import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsUnfoldingTorus
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsUnfoldAlongSubgroup
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsHaarParabolicCoordinates
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsStabilizerCovolume
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PScalingLaw
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PArchLatticeDiscrete

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [NumberField F] [NumberField E] [IsTotallyReal F] [IsTotallyComplex E] in

theorem invApply_mul {h : HermitianForm F E W} {v : Basis ι E W} (a b : archUnitary h v)
    (y : InfinitePlace E → ι → ℂ) : invApply (a * b) y = invApply b (invApply a y) := by
  funext w
  simp only [invApply, _root_.mul_inv_rev, Subgroup.coe_mul, Pi.mul_apply, Units.val_mul,
    Matrix.mulVec_mulVec]

omit [NumberField F] [NumberField E] [IsTotallyReal F] [IsTotallyComplex E] in

theorem invApply_of_mem_vecFixGroup {h : HermitianForm F E W} {v : Basis ι E W} {x₀ : W}
    {x : archUnitary h v} (hx : x ∈ vecFixGroup h v x₀) : invApply x (vecAt v x₀) = vecAt v x₀ :=
  funext fun w => mem_vecFixGroup.1 (inv_mem hx) w

omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E] in

theorem len_invApply_of_mem_stab {h : HermitianForm F E W} {v : Basis ι E W} (M : Majorant h v)
    {k : archUnitary h v} (hk : k ∈ M.stab) (y : InfinitePlace E → ι → ℂ) :
    M.len (invApply k y) = M.len y := by
  unfold Majorant.len
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  have hk' := inv_mem hk
  rw [Majorant.stab, Subgroup.mem_subgroupOf] at hk'
  have hA := mem_unitaryGroupMatrix.1 ((Subgroup.mem_pi _).1 hk' w (Set.mem_univ w))
  set A : Matrix ι ι ℂ := (((k⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)
    with hA_def
  have hA' : Aᴴ * M.P w * A = M.P w := hA
  simp only [invApply]
  rw [← hA_def, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, hA']

omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E] in

theorem vecStabGroup_le_vecFixGroup [NumberField F] [IsTotallyReal F] [IsTotallyComplex E]
    (h : HermitianForm F E W) (v : Basis ι E W) (La : AddSubgroup W) (x₀ : W) :
    vecStabGroup h v La x₀ ≤ vecFixGroup h v x₀ := by
  rintro _ ⟨γ, hγ, rfl⟩
  have e := archEmbed_smul_vecAt h v (γ : h.unitaryGroup) x₀
  rw [show (γ : h.unitaryGroup) • x₀ = x₀ from MulAction.mem_stabilizer_iff.1 hγ] at e
  exact fun w => congrFun e w

theorem ae_forall_ne_zero (κ : Type*) [Fintype κ] : ∀ᵐ b : κ → ℂ, ∀ w, b w ≠ 0 := by
  rw [ae_all_iff]
  intro w
  have h0 : volume ((fun b : κ → ℂ => b w) ⁻¹' {0}) = 0 :=
    Measure.pi_eval_preimage_null _ (measure_singleton 0)
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with b hb
  exact hb

theorem UnfoldingTorus.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : ∀ M : Majorant h v,
      UnfoldAlongSubgroup.Statement (archUnitary h v) ((InfinitePlace E → ℂ) × M.stab))
    (h₂ : HaarParabolicCoordinates.Statement h v) (h₃ : StabilizerCovolumeFinite.Statement h v) :
    UnfoldingTorus.Statement h v := by
  intro M μ _ D La x₀ hLa hx₀ hne hiso
  obtain ⟨ν, κ, τ, hν, -, hκ, hτm, hτ, hμ⟩ := h₂ M μ x₀ hne hiso
  obtain ⟨FD₀, hFD₀, h0, htop⟩ := h₃ D La x₀ hLa hx₀ hne hiso ν hν
  refine ⟨ν FD₀, h0, htop, fun FD hFD t ht => ?_⟩
  set y₀ := vecAt v x₀ with hy₀
  set wt : (InfinitePlace E → ℂ) → ℝ≥0∞ := fun b => ∏ w, ‖b w‖ₑ ^ (2 * (finrank E W - 2))
    with hwt
  set S := {g : archUnitary h v | M.len (invApply g y₀) < t} with hS_def
  set T := {b : InfinitePlace E → ℂ | M.len (fun w => b w • y₀ w) < t} with hT_def
  have hS : MeasurableSet S := measurableSet_below M y₀ t

  have : SecondCountableTopology (vecStabGroup h v La x₀) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have : DiscreteTopology (vecStabGroup h v La x₀) := by
    have := ArchLatticeDiscrete.proof h v La hLa.isLattice
    have hle : vecStabGroup h v La x₀ ≤ archLatticeGroup h v La := by
      rintro _ ⟨γ, -, rfl⟩
      exact ⟨(γ : h.unitaryGroup), γ.2, rfl⟩
    exact DiscreteTopology.of_continuous_injective (f := Subgroup.inclusion hle)
      (continuous_subtype_val.subtype_mk _) (Subgroup.inclusion_injective hle)
  have : Countable (vecStabGroup h v La x₀) :=
    TopologicalSpace.separableSpace_iff_countable.1 inferInstance

  let s : (InfinitePlace E → ℂ) × M.stab → archUnitary h v := fun y => τ y.1 * y.2
  have hwtm : Measurable wt :=
    Finset.measurable_prod _ fun w _ => (measurable_pi_apply w).enorm.pow_const _
  have hsm' : Measurable s := (hτm.comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd)
  have hsm : Measurable fun p : vecFixGroup h v x₀ × ((InfinitePlace E → ℂ) × M.stab) =>
      (p.1 : archUnitary h v) * s p.2 :=
    (measurable_subtype_coe.comp measurable_fst).mul (hsm'.comp measurable_snd)
  have hform : ∀ f : archUnitary h v → ℝ≥0∞, Measurable f → ∫⁻ g, f g ∂μ =
      ∫⁻ y, ∫⁻ x, f (x * s y) ∂ν ∂((volume.withDensity wt).prod κ) := by
    intro f hf
    have hin : Measurable fun y => ∫⁻ x : vecFixGroup h v x₀, f (x * s y) ∂ν :=
      (hf.comp hsm).lintegral_prod_left'
    rw [hμ f hf, lintegral_prod _ hin.aemeasurable,
      lintegral_withDensity_eq_lintegral_mul _ hwtm hin.lintegral_prod_right']
    rfl

  have hf : Measurable (S.indicator (1 : archUnitary h v → ℝ≥0∞)) := measurable_one.indicator hS
  have hinv : ∀ x : vecFixGroup h v x₀, ∀ g,
      S.indicator (1 : archUnitary h v → ℝ≥0∞) (x * g) = S.indicator 1 g := by
    intro x g
    have hx : invApply (x : archUnitary h v) y₀ = y₀ := invApply_of_mem_vecFixGroup x.2
    simp only [hS_def, Set.indicator_apply, Set.mem_ofPred_eq, invApply_mul, hx, Pi.one_apply]
  have key := h₁ M μ (vecFixGroup h v x₀) ν ((volume.withDensity wt).prod κ) s hsm hform
    (vecStabGroup h v La x₀) (vecStabGroup_le_vecFixGroup h v La x₀) FD FD₀ hFD hFD₀ _ hf hinv
  rw [Set.inter_comm, ← Measure.restrict_apply hS, ← lintegral_indicator_one hS, key]
  congr 1

  have hmS : Measurable fun y => S.indicator (1 : archUnitary h v → ℝ≥0∞) (s y) := hf.comp hsm'
  rw [lintegral_prod _ hmS.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul _ hwtm hmS.lintegral_prod_right']
  refine lintegral_congr_ae ?_
  filter_upwards [ae_forall_ne_zero (InfinitePlace E)] with b hb
  have hk : ∀ k : M.stab, S.indicator (1 : archUnitary h v → ℝ≥0∞) (s (b, k)) =
      T.indicator 1 b := by
    intro k
    simp only [s, Set.indicator_apply, hS_def, hT_def, Set.mem_ofPred_eq, invApply_mul, hτ b hb,
      len_invApply_of_mem_stab M k.2, Pi.one_apply]
  simp only [Pi.mul_apply, hk, lintegral_const, measure_univ, mul_one]
  by_cases hbT : b ∈ T
  · simp [Set.indicator_of_mem hbT]
  · simp [Set.indicator_of_notMem hbT]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
