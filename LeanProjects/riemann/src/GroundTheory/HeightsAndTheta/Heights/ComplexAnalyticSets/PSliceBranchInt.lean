import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceBranchInt
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StParamChartInt
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchProperAtPoint
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceImmersiveGeneral
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLinearNoetherNormalization
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

namespace SliceBranchInt

open ReciprocityTheory.AnForm.A (hypIncl)

theorem norm_hypIncl {d : ℕ} (w : Fin d → ℂ) : ‖hypIncl w‖ = ‖w‖ := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg w)).2 fun i => ?_)
    ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_)
  · refine Fin.cases ?_ (fun j => ?_) i
    · simp [hypIncl]
    · simpa [hypIncl] using norm_le_pi_norm w j
  · simpa [hypIncl] using norm_le_pi_norm (hypIncl w) j.succ

theorem differentiable_hypIncl {d : ℕ} : Differentiable ℂ (hypIncl : (Fin d → ℂ) → Fin (d + 1) → ℂ) := by
  refine differentiable_pi.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [hypIncl, Fin.cons_zero]
    exact differentiable_const _
  · simp only [hypIncl, Fin.cons_succ]
    exact differentiable_apply j

theorem hypIncl_tail {d : ℕ} (t : Fin (d + 1) → ℂ) (ht : t 0 = 0) :
    hypIncl (Fin.tail t) = t ∧ ‖Fin.tail t‖ ≤ ‖t‖ := by
  refine ⟨?_, (pi_norm_le_iff_of_nonneg (norm_nonneg t)).2 fun j => norm_le_pi_norm t j.succ⟩
  rw [hypIncl, ← ht]
  exact Fin.cons_self_tail t

end SliceBranchInt

open ReciprocityTheory.AnForm.A (hypIncl densHyp) in

theorem SliceBranchInt.proof (hBP : IndefiniteRowSideFullHecke.ComplexSets.BranchProperAtPoint.Statement)
    (hPCI : ParamChartInt.Statement) : SliceBranchInt.Statement := by
  classical
  intro n d J W u q m γ ord hJ hdim hu hW hq ⟨N₁, hN₁, h₁⟩ hcov ⟨N₃, hN₃, h₃⟩ hmeet hord
  have hWdim := IndefiniteRowSideFullHecke.ComplexSets.dim_component_linForm hJ hdim hu hW
  have hJW : J ≤ W := le_sup_left.trans hW.1.2
  have hex := ComplexSets.LinearNoetherNormalization.proof n d W hWdim
  have hr : ∀ b, 0 < (γ b).radius / 2 := fun b => half_pos (γ b).radius_pos
  have hP := fun b => hBP n (d + 1) J u q q m γ hJ hdim hu hcov hmeet b 0
    (Metric.mem_ball_self (γ b).radius_pos) (γ b).map_zero _ (Metric.closedBall_mem_nhds 0 (hr b))
  choose ε hε hprop using hP
  set N := interior N₁ ∩ interior N₃ ∩ ⋂ b, Metric.ball q (ε b) with hNdef
  have hNo : IsOpen N :=
    (isOpen_interior.inter isOpen_interior).inter (isOpen_iInter_of_finite fun b => Metric.isOpen_ball)
  refine ⟨N, hNo.mem_nhds ⟨⟨mem_interior_iff_mem_nhds.2 hN₁, mem_interior_iff_mem_nhds.2 hN₃⟩,
    Set.mem_iInter.2 fun b => Metric.mem_ball_self (hε b)⟩, fun b f φ hf hfc hfN hφ => ?_⟩

  have huq : linEval u q = 0 := by
    have := hq _ ((le_sup_right.trans hW.1.2) (Ideal.mem_span_singleton_self (linForm u)))
    simpa [linForm, linEval] using this
  obtain ⟨H, -, hH0, hHF⟩ := hord b
  have hHF' : ∀ t ∈ Metric.ball (0 : Fin (d + 1) → ℂ) (γ b).radius,
      linEval u ((γ b).toFun t) = t 0 ^ ord b * H t := hHF
  have hord0 : ord b ≠ 0 := by
    intro h0
    have := hHF' 0 (Metric.mem_ball_self (γ b).radius_pos)
    rw [(γ b).map_zero, huq, h0, pow_zero, one_mul] at this
    exact hH0 0 (Metric.mem_ball_self (γ b).radius_pos) this.symm
  have hball : ∀ w ∈ Metric.ball (0 : Fin d → ℂ) (γ b).radius, hypIncl w ∈ Metric.ball 0 (γ b).radius :=
    fun w hw => by rwa [Metric.mem_ball, dist_zero_right, SliceBranchInt.norm_hypIncl, ← dist_zero_right]
  have hA := hPCI n d W hex.choose (fun w => (γ b).toFun (hypIncl w)) (γ b).radius ((γ b).radius / 2) N
    hW.1.1 hWdim hex.choose_spec
    ((γ b).differentiableOn.comp SliceBranchInt.differentiable_hypIncl.differentiableOn hball)
    (fun w hw w' hw' h => by
      have := (γ b).injOn (hball w hw) (hball w' hw') h
      simpa [hypIncl] using congrArg Fin.tail this)
    hNo (half_lt_self (γ b).radius_pos) (fun w hw hN => ⟨h₁ _ ⟨(γ b).mapsTo (hball w hw),
        interior_subset hN.1.1⟩ (by rw [hHF' _ (hball w hw), ReciprocityTheory.AnForm.A.hypIncl_zero,
          zero_pow hord0, zero_mul]), ?_⟩)
    (fun x hx => ?_) f φ hf hfc hfN
    (fun i => by
      obtain ⟨U, hU, hS, hc⟩ := hφ i
      exact ⟨U, hU, (show zeroSet W ⊆ zeroSet J from fun x hx p hp => hx p (hJW hp)).trans hS, hc⟩)
  · unfold varInt
    rw [dif_pos hex, hA]
    rfl
  · have h2 := hprop b (hypIncl w) (hball w hw) (Set.mem_iInter.1 hN.2 b)
    rwa [Metric.mem_closedBall, dist_zero_right, SliceBranchInt.norm_hypIncl] at h2
  · obtain ⟨t, ⟨ht, ht0⟩, rfl⟩ := h₃ b ⟨hx.1, interior_subset hx.2.1.2⟩
    obtain ⟨h1, h2⟩ := SliceBranchInt.hypIncl_tail t ht0
    refine ⟨Fin.tail t, ?_, show (γ b).toFun (hypIncl (Fin.tail t)) = _ by rw [h1]⟩
    rw [Metric.mem_ball, dist_zero_right] at ht ⊢
    exact h2.trans_lt ht

end

end GroundTheory.Heights₂.Heights
