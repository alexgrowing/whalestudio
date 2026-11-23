import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.AnalyticSeries.NeZeroOne
import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.OrderAsym

noncomputable section

namespace UpperTheory.ConvolutionTheory.R

open PositivityTheory.RgJS UpperTheory.ConvolutionTheory.Rs

theorem expRight : ExpRight := by
  intro W q X d A hS x y
  obtain ⟨F, σ₀, hF, he⟩ := hS.rs x y
  refine ⟨F, by simpa using hF 1 one_pos, fun σ hσ => ?_⟩
  classical
  rw [eq_exp hS x y F (fun s => (s - 1) ^ (if x = y then 1 else 0)) σ₀ hF
    (fun t => (analyticAt_id.sub analyticAt_const).pow _) (fun t ht => by rw [he t ht]; split_ifs <;> simp) σ hσ]

theorem logAsym : LogAsym := by
  intro W q X d A hS x y
  obtain ⟨F, σ₀, hF, he⟩ := hS.rs x y
  have hn := exp_re hS x y F σ₀ hF he
  have h0 : ∀ t ∈ Set.Icc (1 : ℝ) 2, ‖F t‖ ≠ 0 := fun t ht => by
    rcases ht.1.eq_or_lt with h | h
    · subst h
      simpa using ne_zero_one hS x y F σ₀ hF he
    · rw [hn t h]
      refine mul_ne_zero ?_ (Real.exp_pos _).ne'
      split_ifs
      · linarith
      · exact one_ne_zero
  have hc : ContinuousOn (fun t : ℝ => Real.log ‖F t‖) (Set.Icc 1 2) := ContinuousOn.log (fun t ht =>
    ((hF t (by linarith [ht.1])).continuousAt.comp (f := fun t : ℝ => (t : ℂ))
      Complex.continuous_ofReal.continuousAt).norm.continuousWithinAt) h0
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨M, fun σ h1 h2 => ?_⟩
  have h := hM σ ⟨h1.le, h2⟩
  rw [hn σ h1, Real.norm_eq_abs] at h
  unfold dre
  split_ifs at h ⊢
  · rw [Real.log_mul (by linarith) (Real.exp_pos _).ne', Real.log_exp] at h
    rwa [sub_neg_eq_add, add_comm]
  · rwa [one_mul, Real.log_exp, ← sub_zero (Complex.re _)] at h

end UpperTheory.ConvolutionTheory.R
