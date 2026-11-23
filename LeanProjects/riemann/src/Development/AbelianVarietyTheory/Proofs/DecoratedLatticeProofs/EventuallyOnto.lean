import Mathlib

open scoped Topology
open Filter

namespace GlobalTheory.ApproxOnto

theorem eventually_onto : ∀ (X : Type) (W : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ W] (T : ℕ → W →ₗ[ℂ] W), (∀ (ψ : W) (x : X), Tendsto (fun i => (T i ψ).1 x) atTop (𝓝 (ψ.1 x))) → ∃ i, Function.Surjective (T i) := by
  intro X W _ T hT
  have hconv : ∀ ψ : W, Tendsto (fun i => T i ψ) atTop (𝓝 ψ) := by
    intro ψ
    rw [tendsto_subtype_rng]
    exact tendsto_pi_nhds.2 (fun x => hT ψ x)
  let b := Module.finBasis ℂ W
  have hmat : Tendsto (fun i => LinearMap.toMatrix b b (T i)) atTop
      (𝓝 (LinearMap.toMatrix b b LinearMap.id)) := by
    refine tendsto_pi_nhds.2 fun k => tendsto_pi_nhds.2 fun j => ?_
    simp only [LinearMap.toMatrix_apply]
    have hc : Continuous (fun w : W => b.repr w k) := (b.coord k).continuous_of_finiteDimensional
    exact (hc.tendsto _).comp (hconv (b j))
  have hdet : Tendsto (fun i => LinearMap.det (T i)) atTop (𝓝 1) := by
    have := ((continuous_id.matrix_det).tendsto _).comp hmat
    simpa [LinearMap.det_toMatrix, Function.comp_def] using this
  obtain ⟨i, hi⟩ := (hdet.eventually_ne one_ne_zero).exists
  refine ⟨i, ?_⟩
  have hu : IsUnit (T i) := (LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hi)
  exact ((Module.End.isUnit_iff _).1 hu).2

end GlobalTheory.ApproxOnto
