import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StarMulOfMemKc

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory
open Filter Topology

namespace GlobalTheory.CartanInt.ExpLocal

attribute [local instance] GlobalTheory.CompactDualExists.sumNormedAddCommGroup
  GlobalTheory.CompactDualExists.sumNormedSpace

theorem l1_eq_norm {n : Type} [Fintype n] (A : Matrix n n ℂ) : l1 A = ‖A‖ :=
  (GlobalTheory.CompactDualExists.sum_norm_def A).symm

theorem exists_exp_approx (n : Type) [Fintype n] [DecidableEq n] :
    ∃ r : ℝ, 0 < r ∧ ∀ Y : Matrix n n ℂ, ‖Y‖ < r →
      ‖NormedSpace.exp Y - 1 - Y‖ ≤ 1 / 21 * ‖Y‖ := by
  have h := (GlobalTheory.CompactDualExists.exp_strict (n := n)).hasFDerivAt
  have h2 := h.isLittleO.def (c := 1 / 21) (by norm_num)
  obtain ⟨r, hr, H⟩ := Metric.eventually_nhds_iff_ball.1 h2
  refine ⟨r, hr, fun Y hY => ?_⟩
  have h3 := H Y (mem_ball_zero_iff.2 hY)
  rw [NormedSpace.exp_zero, sub_zero] at h3
  exact h3

theorem exp_log_near_one : ∀ (p q : ℕ), ∃ ρ : ℝ, 0 < ρ ∧ (∀ Y : Mat p q, l1 Y < ρ → l1 (NormedSpace.exp Y - 1) ≤ 21 / 20 * l1 Y) ∧ ∀ g : UpqT p q, l1 (UpqT.mat g - 1) < ρ → ∃ X : lieU p q, UpqT.mat g = NormedSpace.exp (X : Mat p q) ∧ l1 (X : Mat p q) ≤ 21 / 20 * l1 (UpqT.mat g - 1) := by
  intro p q
  obtain ⟨r, hr, H⟩ := exists_exp_approx (Fin p ⊕ Fin q)
  have hN := GlobalTheory.ExpBallNhds.exp_ballU_mem_nhds p q r hr
  rw [GlobalTheory.UpqTopology.isInducing_mat.nhds_eq_comap, Filter.mem_comap] at hN
  obtain ⟨T, hT, hsub⟩ := hN
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hT
  refine ⟨min r ε, lt_min hr hε, fun Y hY => ?_, fun g hg => ?_⟩
  · rw [l1_eq_norm] at hY
    rw [l1_eq_norm, l1_eq_norm]
    have h1 := H Y (hY.trans_le (min_le_left _ _))
    have h2 := norm_le_norm_add_norm_sub' (NormedSpace.exp Y - 1) Y
    have h3 := norm_nonneg Y
    linarith
  · rw [l1_eq_norm] at hg
    have hg' : UpqT.mat g ∈ Metric.ball (UpqT.mat (1 : UpqT p q)) ε := by
      rw [mem_ball_iff_norm, mat_one]
      exact hg.trans_le (min_le_right _ _)
    obtain ⟨X, hX, hgX⟩ := hsub (show g ∈ UpqT.mat ⁻¹' T from hball hg')
    refine ⟨X, hgX, ?_⟩
    have hX' : l1 (X : Mat p q) < r := hX
    rw [l1_eq_norm] at hX'
    rw [l1_eq_norm, l1_eq_norm, hgX]
    have h1 := H X hX'
    have h2 := norm_le_norm_add_norm_sub (NormedSpace.exp (X : Mat p q) - 1) (X : Mat p q)
    linarith

end GlobalTheory.CartanInt.ExpLocal
