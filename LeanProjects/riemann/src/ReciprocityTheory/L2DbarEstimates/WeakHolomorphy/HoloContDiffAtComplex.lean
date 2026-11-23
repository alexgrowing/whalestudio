import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.ExistsClmOfI

namespace ReciprocityTheory.L2DbarEstimates.C

open Metric Set Filter Topology Complex
open scoped ContDiff

theorem holoContDiff : HoloContDiffStatement := by
  intro n Ω f hΩ hf
  rw [contDiffOn_infty]
  intro k
  induction k generalizing f with
  | zero =>
    rw [Nat.cast_zero, contDiffOn_zero]
    exact hf.continuousOn
  | succ k ih =>
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hΩ]
    refine ⟨hf, fun h => absurd h (by simp), ?_⟩
    rw [contDiffOn_clm_apply]
    intro v
    exact ih _ (holoDeriv n Ω f hΩ hf v)

theorem holo_contDiffOn_complex {n : ℕ} {Ω : Set (EuclideanSpace ℂ (Fin n))}
    {f : EuclideanSpace ℂ (Fin n) → ℂ} (hΩ : IsOpen Ω) (hf : DifferentiableOn ℂ f Ω) :
    ContDiffOn ℂ ∞ f Ω := holoContDiff _ Ω f hΩ hf

theorem holo_contDiffAt_complex {n : ℕ} {Ω : Set (EuclideanSpace ℂ (Fin n))}
    {f : EuclideanSpace ℂ (Fin n) → ℂ} (hΩ : IsOpen Ω) (hf : DifferentiableOn ℂ f Ω)
    {x : EuclideanSpace ℂ (Fin n)} (hx : x ∈ Ω) (k : ℕ) : ContDiffAt ℂ k f x := (contDiffOn_infty.1 (holoContDiff _ Ω f hΩ hf) k).contDiffAt (hΩ.mem_nhds hx)

end ReciprocityTheory.L2DbarEstimates.C
