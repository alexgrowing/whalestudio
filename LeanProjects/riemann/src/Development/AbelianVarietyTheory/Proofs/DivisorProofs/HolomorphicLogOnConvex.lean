import Mathlib

open Filter Topology

namespace GlobalTheory.ConvexHolLog

theorem exists_differentiableOn_log : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {S : Set F}, Convex ℝ S → IsOpen S → ∀ f : F → ℂ, DifferentiableOn ℂ f S → (∀ x ∈ S, f x ≠ 0) →
    ∃ L : F → ℂ, DifferentiableOn ℂ L S ∧ ∀ x ∈ S, f x = Complex.exp (L x) := by
  intro F _ _ _ S hs ho f hF h0
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, differentiableOn_const _, by simp⟩
  have := hs.contractibleSpace hne
  have hsc : IsSimplyConnected S := (inferInstance : SimplyConnectedSpace S)
  obtain ⟨L, hLc, hL⟩ := Complex.exists_continuousOn_eqOn_exp_comp hsc ho hF.continuousOn
    (by rintro ⟨w, hw, h⟩; exact h0 w hw h)
  refine ⟨L, fun w hw => ?_, fun w hw => (hL hw).symm⟩
  have hn := ho.mem_nhds hw
  have hc : ContinuousAt (fun z => (L z - L w).im) w :=
    Complex.continuous_im.continuousAt.comp ((hLc.continuousAt hn).sub continuousAt_const)
  have h1 : ∀ᶠ z in 𝓝 w, (L z - L w).im ∈ Set.Ioo (-Real.pi) Real.pi :=
    hc.eventually (isOpen_Ioo.mem_nhds (by simp [Real.pi_pos]))
  have h2 : L =ᶠ[𝓝 w] fun z => L w + Complex.log (f z / f w) := by
    filter_upwards [h1, hn] with z hz hzS
    rw [← hL hzS, ← hL hw, Function.comp, Function.comp, ← Complex.exp_sub, Complex.log_exp hz.1 hz.2.le]
    ring
  refine (DifferentiableAt.congr_of_eventuallyEq ?_ h2).differentiableWithinAt
  have h3 : DifferentiableAt ℂ (fun z => f z / f w) w := by
    simp only [div_eq_mul_inv]
    exact (hF.differentiableAt hn).mul_const _
  refine DifferentiableAt.const_add _ (DifferentiableAt.comp (g := Complex.log) w (Complex.differentiableAt_log ?_) h3)
  simp [div_self (h0 w hw)]

end GlobalTheory.ConvexHolLog
