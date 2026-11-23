import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Regularisation.StatementsTruncPsh
import GroundTheory.HeightsAndTheta.Heights.Regularisation.GlueCharts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric Filter Topology Set
open ReciprocityTheory.AnForm.A (IsPsh coordDiv limsupExt)
open ReciprocityTheory.AnForm.M (FinHolAtlas)

noncomputable section

namespace RegChartData

variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X} (R : RegChartData A)

theorem one_le_log_growth (j : Fin R.N) {y : Fin D → ℂ} (hyt : y ∈ (R.chart j).target) :
    1 ≤ Real.log (Real.exp 1 + ∑ i ∈ R.S j, Real.log ‖y i‖⁻¹) := by
  have hy1 : ‖y‖ < 1 := by simpa using R.target_subset j hyt
  have hs : 0 ≤ ∑ i ∈ R.S j, Real.log ‖y i‖⁻¹ := Finset.sum_nonneg fun i _ => by
    rw [Real.log_inv]
    exact neg_nonneg.2 (Real.log_nonpos (norm_nonneg _) ((norm_le_pi_norm y i).trans hy1.le))
  have := Real.log_le_log (Real.exp_pos 1) (le_add_of_nonneg_right hs (a := Real.exp 1))
  rwa [Real.log_exp] at this

theorem trunc_psh_le (j : Fin R.N) {V : Set (Fin D → ℂ)} (hV : IsOpen V)
    (hVt : V ⊆ (R.chart j).target) {B : ℝ} (hB : ∀ y ∈ V \ coordDiv (R.S j), R.u j y ≤ B)
    (K : ℝ) : IsPsh V (R.trunc K j) ∧ ∀ y ∈ V, R.trunc K j y ≤ max B (-K) := by
  have hcont : ContinuousOn (R.u j) (V \ coordDiv (R.S j)) :=
    (R.continuousOn_u j).mono (sdiff_subset_sdiff_left hVt)
  have hpsh : IsPsh (V \ coordDiv (R.S j)) (R.u j) :=
    isPsh_mono (R.u_psh j) (sdiff_subset_sdiff_left hVt)
  have hbound : ∀ y ∈ V \ coordDiv (R.S j), R.u j y ≤
      |B| * Real.log (Real.exp 1 + ∑ i ∈ R.S j, Real.log ‖y i‖⁻¹) := fun y hy =>
    (hB y hy).trans ((le_abs_self B).trans
      (le_mul_of_one_le_right (abs_nonneg _) (R.one_le_log_growth j (hVt hy.1))))
  have hext := (ReciprocityTheory.AnForm.A.pshExtension_thm D (R.S j) V (R.u j) |B| hV
    (hVt.trans (R.target_subset j)) hcont hpsh hbound).2 K

  have heq : EqOn (limsupExt V (coordDiv (R.S j)) (fun y => max (R.u j y) (-K)))
      (R.trunc K j) V := by
    intro y hy
    simp only [RegChartData.trunc, limsupExt]
    split_ifs with hA
    · congr 1
      rw [nhdsWithin_restrict ((R.chart j).target \ coordDiv (R.S j)) hy hV]
      congr 1
      ext v
      constructor
      · rintro ⟨hv1, hv2⟩; exact ⟨⟨hVt hv1, hv2⟩, hv1⟩
      · rintro ⟨⟨-, hv2⟩, hv1⟩; exact ⟨hv1, hv2⟩
    · rfl
  refine ⟨isPsh_congr heq hext, fun y hy => ?_⟩
  by_cases hA : y ∈ coordDiv (R.S j)
  · simp only [RegChartData.trunc, limsupExt, if_pos hA]
    have := ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.nebot_diff (S := R.S j) (R.chart j).open_target (hVt hy)
    refine limsup_le_of_le (isCoboundedUnder_le_of_le _ fun v => le_max_right (R.u j v) (-K)) ?_
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hy), self_mem_nhdsWithin]
      with v hv hvt
    exact max_le_max (hB v ⟨hv, hvt.2⟩) le_rfl
  · simp only [RegChartData.trunc, limsupExt, if_neg hA]
    exact max_le_max (hB y ⟨hy, hA⟩) le_rfl

end RegChartData

theorem TruncPsh.proof : TruncPsh.Statement := by
  intro X _ _ _ D A R
  have hKc : ∀ j, IsCompact (R.chart j '' closure (R.mid j)) := fun j =>
    isClosed_closure.isCompact.image_of_continuousOn
      ((R.chart j).continuousOn.mono (R.closure_mid j))
  have hKt : ∀ j, R.chart j '' closure (R.mid j) ⊆ (R.chart j).target := fun j =>
    image_subset_iff.2 fun x hx => (R.chart j).map_source (R.closure_mid j hx)
  have hε : ∀ j, ∃ ε, 0 < ε ∧
      cthickening ε (R.chart j '' closure (R.mid j)) ⊆ (R.chart j).target := fun j =>
    (hKc j).exists_cthickening_subset_open (R.chart j).open_target (hKt j)
  choose ε hεpos hεsub using hε
  have hM : ∀ j, ∃ M, ∀ y ∈ cthickening (ε j) (R.chart j '' closure (R.mid j)), R.q j y ≤ M := by
    intro j
    obtain ⟨M, hM⟩ := (hKc j).cthickening.bddAbove_image
      ((R.q_smooth j).continuousOn.mono (hεsub j))
    exact ⟨M, fun y hy => hM ⟨y, hy, rfl⟩⟩
  choose M hM using hM
  obtain ⟨δ, hδε, hδ⟩ := ((Filter.eventually_all.2 fun j =>
    (eventually_lt_nhds (hεpos j)).filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioi 0)).exists
  have hVt : ∀ j, thickening (ε j) (R.chart j '' closure (R.mid j)) ⊆ (R.chart j).target :=
    fun j => (thickening_subset_cthickening _ _).trans (hεsub j)
  refine ⟨δ, ∑ k, |M k| + |R.Cph|, hδ, fun j => ⟨_, isOpen_thickening, hVt j,
    fun x hx y hy => ?_, fun K => R.trunc_psh_le j isOpen_thickening (hVt j) ?_ K⟩⟩
  · exact mem_thickening_iff.2 ⟨_, ⟨x, subset_closure hx, rfl⟩,
      (mem_closedBall.1 hy).trans_lt (hδε j)⟩
  · intro y hy
    have h1 : R.q j y ≤ M j := hM j y (thickening_subset_cthickening _ _ hy.1)
    have h2 : R.ph ((R.chart j).symm y) ≤ R.Cph := R.ph_le _ (R.symm_mem_Yo j (hVt j hy.1) hy.2)
    have h3 : |M j| ≤ ∑ k, |M k| :=
      Finset.single_le_sum (f := fun k => |M k|) (fun k _ => abs_nonneg _) (Finset.mem_univ j)
    have : R.u j y = R.q j y + R.ph ((R.chart j).symm y) := rfl
    rw [this]
    linarith [le_abs_self (M j), le_abs_self R.Cph]

end

end GroundTheory.Heights₂.Heights.Regular
