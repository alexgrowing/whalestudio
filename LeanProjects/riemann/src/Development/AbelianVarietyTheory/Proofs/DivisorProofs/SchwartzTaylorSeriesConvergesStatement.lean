import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzTaylorSeriesConverges
import Mathlib
open SchwartzMap Filter Topology
open scoped Nat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_taylor_series_converges : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (ψ : SchwartzMap V ℂ) (A ρ : ℝ), (∀ (j : ℕ) (y : V), ‖iteratedFDeriv ℝ j ψ y‖ ≤ A * ρ ^ j) →
    ∀ x : V, Tendsto (fun m : ℕ => ∑ j ∈ Finset.range (m + 1),
      ((j ! : ℝ))⁻¹ • iteratedFDeriv ℝ j ψ 0 (fun _ => x)) atTop (𝓝 (ψ x)) := by
  first | exact @GlobalTheory.tendsto_taylor_sum_of_deriv_bound | exact GlobalTheory.tendsto_taylor_sum_of_deriv_bound | (intros; apply GlobalTheory.tendsto_taylor_sum_of_deriv_bound <;> assumption)
