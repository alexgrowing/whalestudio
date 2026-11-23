import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeaklyConvergentSchwartzBounded
import Mathlib
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weakly_convergent_schwartz_bounded : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (f : ℕ → SchwartzMap V ℂ) (f₀ : SchwartzMap V ℂ), (∀ T : SchwartzMap V ℂ →L[ℂ] ℂ, Tendsto (fun j => T (f j)) atTop (𝓝 (T f₀))) → ∀ k n : ℕ, BddAbove (Set.range fun j => SchwartzMap.seminorm ℂ k n (f j)) := by
  first | exact @GlobalTheory.SchwartzMap.bddAbove_seminorm_of_weak_tendsto | exact GlobalTheory.SchwartzMap.bddAbove_seminorm_of_weak_tendsto | (intros; apply GlobalTheory.SchwartzMap.bddAbove_seminorm_of_weak_tendsto <;> assumption)
