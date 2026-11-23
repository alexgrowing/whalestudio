import Mathlib

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.HolA

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
variable {Kg : Type*} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg] [BorelSpace Kg]
  {μ : Measure Kg} [IsFiniteMeasure μ]

theorem integrable_of_cont {W : Type*} [NormedAddCommGroup W] {f : Kg → W} (hf : Continuous f) :
    Integrable f μ := by
  have hm : AEStronglyMeasurable f μ := by
    simpa using (hf.continuousOn (s := univ)).aestronglyMeasurable_of_isCompact isCompact_univ
      MeasurableSet.univ (μ := μ)
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (hf.continuousOn (s := univ))
  exact Integrable.of_bound hm C (Eventually.of_forall fun k => hC k (mem_univ k))

theorem hasFDerivAt_int {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
    {Ω : Set E} (hΩ : IsOpen Ω) {Φ : Kg → E → W} {Φ' : Kg → E → (E →L[ℂ] W)}
    (hc : ContinuousOn (fun y : Kg × E => Φ y.1 y.2) (univ ×ˢ Ω))
    (hc' : ContinuousOn (fun y : Kg × E => Φ' y.1 y.2) (univ ×ˢ Ω))
    (hd : ∀ k, ∀ x ∈ Ω, HasFDerivAt (Φ k) (Φ' k x) x) {x₀ : E} (hx₀ : x₀ ∈ Ω) :
    HasFDerivAt (fun x => ∫ k, Φ k x ∂μ) (∫ k, Φ' k x₀ ∂μ) x₀ := by
  obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.mp hΩ x₀ hx₀
  have hsub : closedBall x₀ (r / 2) ⊆ Ω := (closedBall_subset_ball (by linarith)).trans hrΩ
  have hK : IsCompact ((univ : Set Kg) ×ˢ closedBall x₀ (r / 2)) := isCompact_univ.prod (isCompact_closedBall _ _)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hc'.mono (prod_mono subset_rfl hsub))
  have cont_k : ∀ x ∈ Ω, Continuous fun k => Φ k x := fun x hx =>
    continuousOn_univ.mp (hc.comp (f := fun k : Kg => (k, x)) (Continuous.continuousOn (by fun_prop))
      fun k _ => ⟨mem_univ _, hx⟩)
  have cont_k' : ∀ x ∈ Ω, Continuous fun k => Φ' k x := fun x hx =>
    continuousOn_univ.mp (hc'.comp (f := fun k : Kg => (k, x)) (Continuous.continuousOn (by fun_prop))
      fun k _ => ⟨mem_univ _, hx⟩)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ) (F := fun x k => Φ k x)
    (F' := fun x k => Φ' k x) (bound := fun _ => C) (ball_mem_nhds x₀ (half_pos hr)) ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards [hΩ.mem_nhds hx₀] with x hx
    exact (integrable_of_cont (cont_k x hx)).aestronglyMeasurable
  · exact integrable_of_cont (cont_k x₀ hx₀)
  · exact (integrable_of_cont (cont_k' x₀ hx₀)).aestronglyMeasurable
  · exact Eventually.of_forall fun k x hx => hC (k, x) ⟨mem_univ _, ball_subset_closedBall hx⟩
  · exact integrable_const C
  · exact Eventually.of_forall fun k x hx => hd k x (hsub (ball_subset_closedBall hx))

end PositivityTheory.Rg.Sw.LVs.HolA
