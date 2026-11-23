import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsScaledFSHProps
import GroundTheory.HeightsAndTheta.Heights.Intersections.PTorusInvLevi
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 Filter Topology
open GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi (sqSum)
open GroundTheory.Heights₂.Heights.Inter.TorusInvariantLevi (levi_Phi leviForm_phi_nonneg isOpen_noZeroBlock blk)

namespace ScaledFSHProps

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isSmoothHerm : IsSmoothHerm (scaledFSH ι) :=
  (GroundTheory.Heights₂.Heights.Inter.isSmoothHerm_ofMetrics_fs (ι := ι) 1).mul
    (contDiffOn_const (c := Real.exp (-(-1 : ℝ))))

theorem log_h_eventuallyEq {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    (fun y => Real.log ((scaledFSH ι).h y)) =ᶠ[𝓝 z]
      fun y => (∑ k, Real.log ((fsMetric (ι k)).ρ (fun i => y ⟨k, i⟩))) + 1 := by
  filter_upwards [isOpen_noZeroBlock.mem_nhds hz] with y hy
  have hρ : ∀ k, (fsMetric (ι k)).ρ (fun i => y ⟨k, i⟩) ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hy k
    exact ((fsMetric (ι k)).pos _ fun h0 => hi (congrFun h0 i)).ne'
  rw [scaledFSH_h, Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ => hρ k) (Real.exp_pos 1).ne',
    Real.log_exp, Real.log_prod fun k _ => hρ k]

theorem leviForm_log_h_nonneg {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (w : (Σ k, ι k) → ℂ) :
    0 ≤ leviForm (fun y => Real.log ((scaledFSH ι).h y)) z w := by
  have hd : fderiv ℝ (fun y => Real.log ((scaledFSH ι).h y)) =ᶠ[𝓝 z]
      fderiv ℝ (fun y => ∑ k, Real.log ((fsMetric (ι k)).ρ (fun i => y ⟨k, i⟩))) := by
    filter_upwards [(log_h_eventuallyEq hz).fderiv (𝕜 := ℝ)] with y hy
    rw [hy]
    exact fderiv_add_const (1 : ℝ)
  have hL : leviForm (fun y => Real.log ((scaledFSH ι).h y)) z w =
      leviForm (fun y => ∑ k, Real.log ((fsMetric (ι k)).ρ (fun i => y ⟨k, i⟩))) z w := by
    unfold leviForm
    rw [hd.fderiv_eq]
  rw [hL, levi_Phi hz w]
  refine Finset.sum_nonneg fun k _ => leviForm_phi_nonneg ?_ _
  obtain ⟨i, hi⟩ := hz k
  refine (lt_of_lt_of_le (pow_pos (norm_pos_iff.2 hi) 2) ?_).ne'
  exact Finset.single_le_sum (f := fun j => ‖blk k z j‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)

theorem isSemipositiveRel (P0 P : Ideal (MRing ι)) : IsSemipositiveRel P0 P (scaledFSH ι) :=
  ⟨isSmoothHerm, fun _ hz w _ => leviForm_log_h_nonneg hz.1 w⟩

theorem isConjInvariantH : IsConjInvariantH (scaledFSH ι) := by
  intro z
  rw [scaledFSH_h, scaledFSH_h]
  simp [fsMetric, EuclideanSpace.norm_eq]

theorem norm_le_rho (z : (Σ k, ι k) → ℂ) (k : K) (i : ι k) :
    ‖z ⟨k, i⟩‖ ≤ (fsMetric (ι k)).ρ (fun i => z ⟨k, i⟩) := by
  show ‖z ⟨k, i⟩‖ ≤ ‖WithLp.toLp 2 (fun i => z ⟨k, i⟩)‖
  simpa using PiLp.norm_apply_le (WithLp.toLp 2 (fun i => z ⟨k, i⟩)) i

theorem monomialsBounded (P : Ideal (MRing ι)) : MonomialsBounded P (scaledFSH ι) (fun _ => 1) := by
  intro z _ μ hμ
  rw [scaledFSH_h, norm_prod, Fintype.prod_sigma]
  have hρ : ∀ k, 0 ≤ (fsMetric (ι k)).ρ (fun i => z ⟨k, i⟩) := fun k => norm_nonneg _
  have hblk : ∀ k, ∏ i, ‖z ⟨k, i⟩ ^ μ ⟨k, i⟩‖ ≤ (fsMetric (ι k)).ρ (fun i => z ⟨k, i⟩) := by
    intro k
    calc ∏ i, ‖z ⟨k, i⟩ ^ μ ⟨k, i⟩‖ ≤ ∏ i, (fsMetric (ι k)).ρ (fun i => z ⟨k, i⟩) ^ μ ⟨k, i⟩ := by
          refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_
          rw [norm_pow]
          exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_rho z k i) _
      _ = (fsMetric (ι k)).ρ (fun i => z ⟨k, i⟩) := by
          rw [Finset.prod_pow_eq_pow_sum, hμ k]
          exact pow_one _
  calc ∏ k, ∏ i, ‖z ⟨k, i⟩ ^ μ ⟨k, i⟩‖ ≤ ∏ k, (fsMetric (ι k)).ρ (fun i => z ⟨k, i⟩) :=
        Finset.prod_le_prod (fun k _ => Finset.prod_nonneg fun i _ => norm_nonneg _) fun k _ => hblk k
    _ ≤ (∏ k, (fsMetric (ι k)).ρ (fun i => z ⟨k, i⟩)) * Real.exp 1 :=
        le_mul_of_one_le_right (Finset.prod_nonneg fun k _ => hρ k) (Real.one_le_exp zero_le_one)

end ScaledFSHProps

theorem ScaledFSHProps.proof : ScaledFSHProps.Statement := fun _ _ _ _ P P0 =>
  ⟨ScaledFSHProps.isSemipositiveRel P0 P, ScaledFSHProps.isConjInvariantH, ScaledFSHProps.monomialsBounded P⟩

end GroundTheory.Heights₂.Heights.HilbertSamuel
