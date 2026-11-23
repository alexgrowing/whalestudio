import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfE

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.HE

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric Filter Complex
open scoped ContDiff ComplexConjugate

noncomputable section

variable {n : ℕ}

def bumpE (ε : ℝ) (hε : 0 < ε) : ContDiffBump (0 : V n) := ⟨ε, 2 * ε, hε, by linarith⟩

def cut (ε : ℝ) (hε : 0 < ε) (y : V n) : ℂ := ((bumpE ε hε : V n → ℝ) y : ℂ)

theorem cut_contDiff (ε : ℝ) (hε : 0 < ε) : ContDiff ℝ ∞ (cut (n := n) ε hε) :=
  Complex.ofRealCLM.contDiff.comp (bumpE ε hε).contDiff

theorem cut_one (ε : ℝ) (hε : 0 < ε) {y : V n} (hy : ‖y‖ ≤ ε) : cut ε hε y = 1 := by
  unfold cut
  rw [(bumpE ε hε).one_of_mem_closedBall (mem_closedBall_zero_iff.mpr hy)]
  simp

theorem cut_zero (ε : ℝ) (hε : 0 < ε) {y : V n} (hy : 2 * ε ≤ ‖y‖) : cut ε hε y = 0 := by
  unfold cut
  rw [(bumpE ε hε).zero_of_le_dist (by rw [dist_zero_right]; exact hy)]
  simp

theorem wdb_const_eq_zero (j : Fin n) (c : ℂ) (y : V n) : wdb n j (fun _ => c) y = 0 := by
  unfold wdb
  simp

theorem wdb_cut_zero (ε : ℝ) (hε : 0 < ε) (j : Fin n) {y : V n}
    (hy : ‖y‖ < ε ∨ 2 * ε < ‖y‖) : wdb n j (cut ε hε) y = 0 := by
  have key : ∀ c : ℂ, (cut ε hε =ᶠ[𝓝 y] fun _ => c) → wdb n j (cut ε hε) y = 0 := by
    intro c hc
    unfold wdb
    rw [hc.fderiv_eq]
    simp
  rcases hy with hy | hy
  · apply key 1
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hy] with z hz
    exact cut_one ε hε (le_of_lt hz)
  · apply key 0
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hy] with z hz
    exact cut_zero ε hε (le_of_lt hz)

theorem wdb_cut_continuous (ε : ℝ) (hε : 0 < ε) (j : Fin n) :
    Continuous (wdb n j (cut ε hε)) := by
  have hc : Continuous (fderiv ℝ (cut (n := n) ε hε)) :=
    (cut_contDiff ε hε).continuous_fderiv (by simp)
  unfold wdb
  exact ((hc.clm_apply continuous_const).add
    (continuous_const.mul (hc.clm_apply continuous_const))).div_const 2

theorem wdb_cut_bdd (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : V n, ∑ j, ‖wdb n j (cut ε hε) y‖ ^ 2 ≤ M := by
  have hcont : Continuous (fun y : V n => ∑ j, ‖wdb n j (cut ε hε) y‖ ^ 2) :=
    continuous_finset_sum _ fun j _ => ((wdb_cut_continuous ε hε j).norm).pow 2
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (0 : V n) (2 * ε)).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun y => ?_⟩
  by_cases hy : ‖y‖ ≤ 2 * ε
  · have h1 := hC y (mem_closedBall_zero_iff.mpr hy)
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun j _ => by positivity)] at h1
    exact h1.trans (le_max_left _ _)
  · push_neg at hy
    have h0 : ∀ j, wdb n j (cut ε hε) y = 0 := fun j => wdb_cut_zero ε hε j (Or.inr hy)
    simp [h0]

theorem norm_pair_sq_le (a ξ : Fin n → ℂ) :
    ‖∑ j, a j * conj (ξ j)‖ ^ 2 ≤ (∑ j, ‖a j‖ ^ 2) * ∑ j, ‖ξ j‖ ^ 2 := by
  have h1 : ‖∑ j, a j * conj (ξ j)‖ ≤ ∑ j, ‖a j‖ * ‖ξ j‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
    simp [norm_mul]
  calc ‖∑ j, a j * conj (ξ j)‖ ^ 2 ≤ (∑ j, ‖a j‖ * ‖ξ j‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.HE
