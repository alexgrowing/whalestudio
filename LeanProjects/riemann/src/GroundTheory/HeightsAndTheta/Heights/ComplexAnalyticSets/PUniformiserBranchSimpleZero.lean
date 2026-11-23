import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StUniformiserBranchSimpleZero
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StUniformiserLocallyInjective
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StInjectiveHolomorphicDerivNeZero
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PointLocalRingOrder
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology

theorem UniformiserBranchSimpleZero.proof (hloc : UniformiserLocallyInjective.Statement)
    (hder : InjectiveHolomorphicDerivNeZero.Statement) : UniformiserBranchSimpleZero.Statement := by
  intro σ _ I w t r φ hI hic hdim ht hr hdiff hinj hmaps hw0
  have hball : ∀ {ρ : ℝ} {τ : ℂ}, τ ∈ Metric.ball (0 : ℂ) ρ →
      (fun _ : Fin 1 ↦ τ) ∈ Metric.ball (0 : Fin 1 → ℂ) ρ := by
    intro ρ τ hτ
    rw [mem_ball_zero_iff] at hτ ⊢
    exact lt_of_le_of_lt (pi_norm_const_le τ) hτ
  have hwZ : w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I := hw0 ▸ hmaps (Metric.mem_ball_self hr)
  have htw : eval w t = 0 := by
    by_contra h
    exact ht.not_isUnit (isUnit_algebraMap_pointLocalRing I w t h)
  obtain ⟨U, hU, hUinj⟩ := hloc σ I w t hI hic hdim hwZ ht
  have hφc : ContinuousAt φ 0 :=
    (hdiff.differentiableAt (Metric.ball_mem_nhds 0 hr)).continuousAt
  have hc1 : Continuous fun τ : ℂ ↦ (fun _ : Fin 1 ↦ τ) := continuous_pi fun _ ↦ continuous_id
  have hcont : ContinuousAt (fun τ : ℂ ↦ φ fun _ ↦ τ) 0 :=
    ContinuousAt.comp_of_eq (g := φ) (f := fun τ : ℂ ↦ (fun _ : Fin 1 ↦ τ)) hφc hc1.continuousAt rfl
  have hpre : (fun τ : ℂ ↦ φ fun _ ↦ τ) ⁻¹' U ∈ 𝓝 (0 : ℂ) :=
    hcont.preimage_mem_nhds (by rw [← hw0] at hU; exact hU)
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hpre (Metric.ball_mem_nhds 0 hr))
  have hfd : DifferentiableOn ℂ (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) t) (Metric.ball 0 ε) :=
    (differentiable_eval_pointLocal t).comp_differentiableOn (hdiff.comp
      (differentiable_pi.2 fun _ ↦ differentiable_id).differentiableOn fun τ hτ ↦ hball (hεU hτ).2)
  have hfi : Set.InjOn (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) t) (Metric.ball 0 ε) := by
    intro a ha b hb hab
    have hab' := hUinj ⟨hmaps (hball (hεU ha).2), (hεU ha).1⟩ ⟨hmaps (hball (hεU hb).2), (hεU hb).1⟩ hab
    exact congrFun (hinj (hball (hεU ha).2) (hball (hεU hb).2) hab') 0
  have hd := hder _ _ Metric.isOpen_ball hfd hfi 0 (Metric.mem_ball_self hε)
  have hf0 : (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) t) 0 = 0 := by
    change eval (φ 0) t = 0
    rw [hw0, htw]
  exact (analyticAt_eval_disc hr hdiff t).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hf0 hd

end GroundTheory.Heights₂.Heights
