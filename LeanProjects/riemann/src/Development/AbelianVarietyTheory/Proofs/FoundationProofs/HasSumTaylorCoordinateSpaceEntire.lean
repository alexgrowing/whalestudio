import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.PderivIterEqPderivListOfDifferentiableOn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LineDerivListCompForm

namespace GlobalTheory.EntireTaylor

theorem summable_of_entire {σ : Type*} [Fintype σ] [DecidableEq σ] {f : (σ → ℂ) → ℂ}
    (hf : Differentiable ℂ f) (c : (σ →₀ ℕ) → ℂ)
    (hc : ∀ α, (∏ j, ((α j).factorial : ℂ)) * c α = pderivIter α f 0) (w : σ → ℂ) :
    Summable fun α : σ →₀ ℕ => c α * ∏ j, w j ^ α j := by
  obtain ⟨R, hRdef⟩ : ∃ R : σ → ℝ, R = fun j => 2 * ‖w j‖ + 1 := ⟨_, rfl⟩
  have hR : ∀ j, 0 < R j := fun j => by rw [hRdef]; positivity
  obtain ⟨M, hM⟩ : ∃ M, ∀ z ∈ Set.univ.pi (fun j => Metric.closedBall (0 : ℂ) (R j)), ‖f z‖ ≤ M :=
    (isCompact_univ_pi fun j => isCompact_closedBall (0 : ℂ) (R j)).exists_bound_of_continuousOn
      hf.continuous.continuousOn
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _)
    (hM 0 (Set.mem_univ_pi.mpr fun j => Metric.mem_closedBall.mpr (by simpa using (hR j).le)))
  have hw : ∀ j, ‖w j‖ / R j ≤ 1 / 2 := fun j => by
    rw [div_le_iff₀ (hR j), hRdef]
    linarith [norm_nonneg (w j)]
  have key : ∀ α : σ →₀ ℕ, ‖c α * ∏ j, w j ^ α j‖ ≤ M * ∏ j, (1 / 2 : ℝ) ^ α j := by
    intro α
    have hP : (∏ j, ((α j).factorial : ℂ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun j _ => by exact_mod_cast Nat.factorial_ne_zero _
    have hcα : c α = pderivIter α f 0 / ∏ j, ((α j).factorial : ℂ) := by
      rw [← hc α, mul_div_cancel_left₀ _ hP]
    have hnormP : ‖∏ j, ((α j).factorial : ℂ)‖ = ∏ j, ((α j).factorial : ℝ) := by
      rw [norm_prod]
      simp
    have hPpos : 0 < ∏ j, ((α j).factorial : ℝ) :=
      Finset.prod_pos fun j _ => by exact_mod_cast Nat.factorial_pos _
    have hC : ‖pderivIter α f 0‖ ≤ (∏ k, ((α k).factorial : ℝ)) * M / ∏ k, R k ^ α k :=
      GlobalTheory.norm_pderivIter_le_of_differentiable α (fun k => (hR k).le) (fun k _ => hR k) hf
        fun z hz => hM z (Set.mem_univ_pi.mpr fun j => Metric.mem_closedBall.mpr (by
          have h := hz j
          simp only [Pi.zero_apply, sub_zero] at h
          rw [dist_zero_right]
          exact h.le))
    have h1 : ‖c α‖ ≤ M / ∏ j, R j ^ α j := by
      rw [hcα, norm_div, hnormP, div_le_iff₀ hPpos]
      calc ‖pderivIter α f 0‖ ≤ (∏ k, ((α k).factorial : ℝ)) * M / ∏ k, R k ^ α k := hC
        _ = (M / ∏ j, R j ^ α j) * ∏ j, ((α j).factorial : ℝ) := by ring
    calc ‖c α * ∏ j, w j ^ α j‖ = ‖c α‖ * ∏ j, ‖w j‖ ^ α j := by
          rw [norm_mul, norm_prod]
          simp [norm_pow]
      _ ≤ (M / ∏ j, R j ^ α j) * ∏ j, ‖w j‖ ^ α j :=
          mul_le_mul_of_nonneg_right h1 (Finset.prod_nonneg fun j _ => by positivity)
      _ = M * ∏ j, (‖w j‖ / R j) ^ α j := by
          simp only [div_pow, Finset.prod_div_distrib]
          ring
      _ ≤ M * ∏ j, (1 / 2 : ℝ) ^ α j :=
          mul_le_mul_of_nonneg_left
            (Finset.prod_le_prod (fun j _ => by have := (hR j).le; positivity)
              fun j _ => pow_le_pow_left₀ (by have := (hR j).le; positivity) (hw j) _) hM0
  exact Summable.of_norm_bounded
    ((GlobalTheory.ProdThetaConj.summable_prod_half_pow (σ := σ)).mul_left M) key

end GlobalTheory.EntireTaylor

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

theorem GlobalTheory.EntireTaylor.hasSum_taylor_mono : ∀ (D : D7) (N N' : ℕ) (F : VC D N N' → ℂ), Differentiable ℂ F → ∀ z : VC D N N', HasSum (fun α : Mono D N N' => Formalism.MainNotions.TaylorLogMetric.taylor D F α * mono D α z) (F z) := by
  intro D N N' F hF z
  have hcd : Differentiable ℂ (fun w => F (GlobalTheory.GaussCauchy.curry D N N' w)) := fun w =>
    (hF _).comp w (LinearMap.toContinuousLinearMap (GlobalTheory.GaussCauchy.curry D N N')).differentiableAt
  have hS := GlobalTheory.EntireTaylor.summable_of_entire hcd (fun α => Formalism.MainNotions.TaylorLogMetric.taylor D F α)
    (fun α => by
      rw [← GlobalTheory.GaussCauchy.factorial_mul_taylor D N N' F hF α, Finsupp.prod_fintype]
      intro i
      simp)
    (fun k => z k.1 k.2.1 k.2.2)
  have hmono : ∀ α : Mono D N N', mono D α z = ∏ k, z k.1 k.2.1 k.2.2 ^ α k := fun α => by
    show (α.prod fun k n => z k.1 k.2.1 k.2.2 ^ n) = _
    rw [Finsupp.prod_fintype]
    intro i
    simp
  have hS' : Summable fun α : Mono D N N' => Formalism.MainNotions.TaylorLogMetric.taylor D F α * mono D α z := by
    simpa only [hmono] using hS
  rw [← GlobalTheory.ProdThetaConj.tsum_taylor_mono D hF z]
  exact hS'.hasSum
