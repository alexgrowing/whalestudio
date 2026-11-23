import Mathlib
import GroundTheory.AutomorphicForms.GKModules.ParametricIntegral

open MeasureTheory
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.ParSmooth

theorem continuous_iteratedFDeriv_partial {P Q E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ψ : P × Q → E) (hΨ : ContDiff ℝ ∞ Ψ) (k : ℕ) :
    Continuous fun z : P × Q => iteratedFDeriv ℝ k (fun y => Ψ (y, z.2)) z.1 := by
  have key : ∀ z : P × Q, iteratedFDeriv ℝ k (fun y => Ψ (y, z.2)) z.1 =
      (iteratedFDeriv ℝ k Ψ z).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inl ℝ P Q) := by
    intro z
    have h1 : (fun y => Ψ (y, z.2)) =
        (fun w => Ψ (((0 : P), z.2) + w)) ∘ ContinuousLinearMap.inl ℝ P Q := by
      funext y; simp
    have h2 : ContDiff ℝ ∞ (fun w => Ψ (((0 : P), z.2) + w)) :=
      hΨ.comp (contDiff_const.add contDiff_id)
    rw [h1, ContinuousLinearMap.iteratedFDeriv_comp_right _ h2 _ (by exact_mod_cast le_top),
      iteratedFDeriv_comp_add_left]
    simp
  simp_rw [key]
  exact (ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ : Fin k => ContinuousLinearMap.inl ℝ P Q)).continuous.comp
    (hΨ.continuous_iteratedFDeriv (by exact_mod_cast le_top))

theorem contDiff_integral_comp_compact {P Q E β : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [TopologicalSpace β] [T2Space β]
    [SecondCountableTopology β] [CompactSpace β] [MeasurableSpace β] [OpensMeasurableSpace β]
    (ν : Measure β) [IsFiniteMeasure ν] (Ψ : P × Q → E) (hΨ : ContDiff ℝ ∞ Ψ) (q : β → Q)
    (hq : Continuous q) : ContDiff ℝ ∞ fun y => ∫ a, Ψ (y, q a) ∂ν := by
  refine GroundTheory.Automorphic.contDiff_integral_of_iteratedFDeriv (μ := ν) (fun y a => Ψ (y, q a))
    (fun a => hΨ.comp (contDiff_id.prodMk contDiff_const)) (fun k => ?_)
    (fun _ => ⟨Set.univ, Filter.univ_mem, Set.univ, isCompact_univ,
      fun _ _ a ha => absurd (Set.mem_univ a) ha⟩)
  have h : Continuous fun p : P × β => (p.1, q p.2) :=
    continuous_fst.prodMk (hq.comp continuous_snd)
  exact (continuous_iteratedFDeriv_partial Ψ hΨ k).comp h

end GlobalTheory.CompanionTheory.ParSmooth
