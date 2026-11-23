import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakBoundedSchwartzTendsto
import Mathlib
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weak_bounded_schwartz_tendsto : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (f : ℕ → SchwartzMap V ℂ) (f₀ : SchwartzMap V ℂ), (∀ T : SchwartzMap V ℂ →L[ℂ] ℂ, Tendsto (fun j => T (f j)) atTop (𝓝 (T f₀))) → (∀ k n : ℕ, BddAbove (Set.range fun j => SchwartzMap.seminorm ℂ k n (f j))) → Tendsto f atTop (𝓝 f₀) := by
  first | exact @GlobalTheory.schwartz_tendsto_of_weak_of_bdd | exact GlobalTheory.schwartz_tendsto_of_weak_of_bdd | (intros; apply GlobalTheory.schwartz_tendsto_of_weak_of_bdd <;> assumption)
