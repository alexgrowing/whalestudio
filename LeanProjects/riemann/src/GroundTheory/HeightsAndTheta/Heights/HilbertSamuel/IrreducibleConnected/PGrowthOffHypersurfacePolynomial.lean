import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IrreducibleConnected.StGrowthOffHypersurfacePolynomial
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IrreducibleConnected.StEntirePolynomialGrowth
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRiemannExtensionAnalytic
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRiemannExtensionAnalytic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

theorem exists_eval_ne_zero_of_isOpen {d : ℕ} {Q : MvPolynomial (Fin d) ℂ} (hQ : Q ≠ 0)
    {V : Set (Fin d → ℂ)} (hV : IsOpen V) (hne : V.Nonempty) : ∃ t ∈ V, eval t Q ≠ 0 := by
  by_contra hall
  simp only [not_exists, not_and, not_not] at hall
  obtain ⟨t, ht⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV t ht
  apply hQ
  refine MvPolynomial.funext_set (fun i => Metric.ball (t i) ε) (fun i => ?_) (fun x hx => ?_)
  · exact infinite_of_mem_nhds (t i) (Metric.ball_mem_nhds (t i) hε)
  · rw [map_zero]
    apply hall
    apply hball
    rw [ball_pi t hε]
    exact hx

theorem dense_eval_ne_zero {d : ℕ} {Q : MvPolynomial (Fin d) ℂ} (hQ : Q ≠ 0) :
    Dense {y : Fin d → ℂ | eval y Q ≠ 0} := by
  rw [dense_iff_inter_open]
  intro V hV hne
  obtain ⟨t, htV, ht⟩ := exists_eval_ne_zero_of_isOpen hQ hV hne
  exact ⟨t, htV, ht⟩

theorem GrowthOffHypersurfacePolynomial.proof (h : EntirePolynomialGrowth.Statement) :
    GrowthOffHypersurfacePolynomial.Statement := by
  intro d Q f C M hQ hf hb
  have hg : Differentiable ℂ (fun y : Fin d → ℂ => eval y Q) := fun y =>
    (AnalyticOnNhd.eval_mvPolynomial Q y (Set.mem_univ y)).differentiableAt
  obtain ⟨F, hF, hFf⟩ := IndefiniteRowSideFullHecke.ComplexSets.RiemannExtensionAnalytic.proof d Set.univ
    (fun y => eval y Q) f isOpen_univ hg.differentiableOn
    (fun V hV _ hne => exists_eval_ne_zero_of_isOpen hQ hV hne)
    (by simpa using hf)
    (fun τ _ => by
      refine ⟨Metric.ball τ 1, Metric.ball_mem_nhds τ one_pos, ?_⟩
      refine isBounded_iff_forall_norm_le.2 ⟨|C| * (2 + ‖τ‖) ^ M, ?_⟩
      rintro _ ⟨y, ⟨⟨hy, -⟩, hyQ⟩, rfl⟩
      have hdist : ‖y‖ ≤ ‖τ‖ + 1 := by
        have := norm_le_norm_add_norm_sub' y τ
        rw [Metric.mem_ball, dist_eq_norm] at hy
        linarith
      calc ‖f y‖ ≤ C * (1 + ‖y‖) ^ M := hb y hyQ
        _ ≤ |C| * (1 + ‖y‖) ^ M :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (by positivity) _)
        _ ≤ |C| * (2 + ‖τ‖) ^ M :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity) (by linarith) M) (abs_nonneg C))
  have hFd : Differentiable ℂ F := differentiableOn_univ.1 hF
  have hFc : Continuous F := hFd.continuous
  have hclosed : IsClosed {y : Fin d → ℂ | ‖F y‖ ≤ C * (1 + ‖y‖) ^ M} :=
    isClosed_le hFc.norm (continuous_const.mul ((continuous_const.add continuous_norm).pow M))
  have hsub : {y : Fin d → ℂ | eval y Q ≠ 0} ⊆ {y | ‖F y‖ ≤ C * (1 + ‖y‖) ^ M} := by
    intro y hy
    have : F y = f y := hFf ⟨Set.mem_univ y, hy⟩
    show ‖F y‖ ≤ C * (1 + ‖y‖) ^ M
    rw [this]
    exact hb y hy
  have hall : ∀ y, ‖F y‖ ≤ C * (1 + ‖y‖) ^ M := by
    intro y
    have := closure_minimal hsub hclosed
    rw [(dense_eval_ne_zero hQ).closure_eq] at this
    exact this (Set.mem_univ y)
  obtain ⟨p, hp⟩ := h d F C M hFd hall
  exact ⟨p, fun y hy => (hFf ⟨Set.mem_univ y, hy⟩).symm.trans (hp y)⟩

end GroundTheory.Heights₂.Heights.HilbertSamuel
