import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshPoisson
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoissonIntegralSmoothOffAxesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PluriharmonicLogGrowthExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviFormZeroExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogBoundDescendsToSmallerSetStatement
open Filter Topology Set Metric MeasureTheory ReciprocityTheory.AnForm
open scoped ContDiff

namespace GlobalTheory.FlatExt

theorem flat_extend : ∀ (e : ℕ) (S : Finset (Fin e)) (c : Fin e → ℂ) (R : ℝ) (f : (Fin e → ℂ) → ℝ), 0 < R → R ≤ 1 → (∀ i ∈ S, c i = 0) → ContDiffOn ℝ ∞ f {z | z ∈ Metric.ball c R ∧ ∀ i ∈ S, z i ≠ 0} → (∀ z ∈ Metric.ball c R, (∀ i ∈ S, z i ≠ 0) → ∀ w, levi f z w = 0) → (∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ z ∈ Metric.ball c R, (∀ i ∈ S, z i ≠ 0) → |f z| ≤ K - ε * ∑ i ∈ S, Real.log ‖z i‖) → ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R ∧ ∃ g : (Fin e → ℂ) → ℝ, ContDiffOn ℝ ∞ g (Metric.ball c ρ) ∧ ∀ z ∈ Metric.ball c ρ, (∀ i ∈ S, z i ≠ 0) → g z = f z := by
  intro e S
  induction S using Finset.induction_on with
  | empty =>
    intro c R f hR _ _ hf _ _
    refine ⟨R, hR, le_rfl, f, ?_, fun z _ _ => rfl⟩
    exact hf.mono fun z hz => ⟨hz, by simp⟩
  | insert i S hi ih =>
    intro c R f hR hR1 hc hf hlev hgr
    have hr : 0 < R / 2 := by linarith
    have hrR : R / 2 < R := by linarith
    have hr1 : R / 2 ≤ 1 := by linarith
    have hci : c i = 0 := hc i (Finset.mem_insert_self _ _)
    have hcS : ∀ k ∈ S, c k = 0 := fun k hk => hc k (Finset.mem_insert_of_mem hk)
    have hg := (GlobalTheory.T.poisson_integral_smooth_off_axes) e S i c R (R / 2) f hr hrR hci hf
    have hag := (GlobalTheory.T.pluriharmonic_log_growth_extension) e S i c R (R / 2) f hr hrR hR1 hci hi hf hlev hgr
    have hlg := (GlobalTheory.T.levi_form_zero_extension) e S i c (R / 2) f _ hg hag (fun z hz hzS hzi w => hlev z (ball_subset_ball hrR.le hz) (by
        intro k hk
        rcases Finset.mem_insert.1 hk with rfl | hk
        · exact hzi
        · exact hzS k hk) w)
    have hbd := (GlobalTheory.T.log_bound_descends_to_smaller_set) e S i c R (R / 2) f hr hrR hci hi hf.continuousOn hgr
    obtain ⟨ρ, hρ, hρR, h, hh, hhg⟩ := ih c (R / 2) _ hr hr1 hcS hg hlg hbd
    refine ⟨ρ, hρ, by linarith, h, hh, ?_⟩
    intro z hz hzS
    have hzS' : ∀ k ∈ S, z k ≠ 0 := fun k hk => hzS k (Finset.mem_insert_of_mem hk)
    rw [hhg z hz hzS']
    exact hag z (ball_subset_ball hρR hz) hzS' (hzS i (Finset.mem_insert_self _ _))

end GlobalTheory.FlatExt
