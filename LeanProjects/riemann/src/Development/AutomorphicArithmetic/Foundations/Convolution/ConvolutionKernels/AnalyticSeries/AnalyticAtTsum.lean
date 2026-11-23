import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.AbsRigClosed

noncomputable section

open scoped ComplexConjugate

namespace UpperTheory.ConvolutionTheory.Rs

open PositivityTheory.RgJS

theorem norm_lterm_re {W A B : Type} [Fintype A] [Fintype B] (q : W → ℕ) (hq : ∀ w, 2 ≤ q w) (α : W → A → ℂ) (β : W → B → ℂ)
    (s : ℂ) (p : W × ℕ) : ‖lterm q α β s p‖ = ‖lterm q α β (s.re : ℝ) p‖ := by
  have h0 : 0 < q p.1 := lt_of_lt_of_le (by norm_num) (hq p.1)
  simp only [lterm, norm_div, norm_mul, norm_pow, Complex.norm_natCast_cpow_of_pos h0, Complex.neg_re, Complex.ofReal_re]

theorem analyticAt_tsum {W A B : Type} [Fintype A] [Fintype B] (q : W → ℕ) (hq : ∀ w, 2 ≤ q w) (α : W → A → ℂ) (β : W → B → ℂ)
    (h : ∀ σ : ℝ, 1 < σ → Summable fun p => ‖lterm q α β σ p‖) (σ : ℝ) (hσ : 1 < σ) :
    AnalyticAt ℂ (fun s => ∑' p, lterm q α β s p) σ := by
  have hU : IsOpen {s : ℂ | (1 + σ) / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ (fun s => ∑' p, lterm q α β s p) {s : ℂ | (1 + σ) / 2 < s.re} := by
    refine Complex.differentiableOn_tsum_of_summable_norm (h ((1 + σ) / 2) (by linarith)) (fun p => ?_) hU fun p s hs => ?_
    · have h0 : (q p.1 : ℂ) ≠ 0 := by
        have := hq p.1
        exact_mod_cast (by omega : q p.1 ≠ 0)
      have h1 : Differentiable ℂ fun s : ℂ => (q p.1 : ℂ) ^ (-s) := differentiable_id.neg.const_cpow (Or.inl h0)
      unfold lterm
      exact (((h1.pow _).const_mul _).div_const _).differentiableOn
    · rw [norm_lterm_re q hq]
      exact DiagonalEntryNormBounds.norm_lterm_anti q hq α β (le_of_lt hs) p
  exact hd.analyticAt (hU.mem_nhds (by simp only [Set.mem_ofPred_eq, Complex.ofReal_re]; linarith))

theorem conv1 : Conv1 := convergence_of_landau_euler landauL euler_product_log_bound

theorem unb : Unb := dirichlet_series_unbounded landauL newton_identities_low_degree euler_product_log_bound removable_singularity_holds conv1

theorem eq_exp {W X : Type} {q : W → ℕ} {d : X → ℕ} {A : ∀ x, W → Fin (d x) → ℂ} (hS : Sys q X d A) (x y : X)
    (F c : ℂ → ℂ) (σ₀ : ℝ) (hF : ∀ σ : ℝ, 0 < σ → AnalyticAt ℂ F σ) (hc : ∀ σ : ℝ, AnalyticAt ℂ c σ)
    (he : ∀ σ : ℝ, σ₀ < σ → F σ = c σ * eul q (A x) (A y) σ) (σ : ℝ) (hσ : 1 < σ) :
    F σ = c σ * Complex.exp (∑' p, lterm q (A x) (A y) σ p) := by
  have h1 : AnalyticOnNhd ℝ (fun t : ℝ => F t) (Set.Ioi 1) := fun t ht =>
    ((hF t (by linarith [Set.mem_Ioi.1 ht])).restrictScalars (𝕜 := ℝ)).comp (Complex.ofRealCLM.analyticAt t)
  have h2 : AnalyticOnNhd ℝ (fun t : ℝ => c t * Complex.exp (∑' p, lterm q (A x) (A y) t p)) (Set.Ioi 1) := fun t ht =>
    (((hc t).mul (analyticAt_tsum q hS.primes.two _ _ (conv1 W q X d A hS x y).1 t ht).cexp).restrictScalars (𝕜 := ℝ)).comp
      (Complex.ofRealCLM.analyticAt t)
  refine h1.eqOn_of_preconnected_of_eventuallyEq h2 isPreconnected_Ioi (z₀ := max σ₀ 2 + 1)
    (Set.mem_Ioi.2 (by linarith [le_max_right σ₀ 2])) ?_ (Set.mem_Ioi.2 hσ)
  filter_upwards [Ioi_mem_nhds (show max σ₀ 2 < max σ₀ 2 + 1 by linarith)] with t ht
  rw [he t (lt_of_le_of_lt (le_max_left _ _) ht), (euler_product_log_bound W q _ _ (A x) (A y) t hS.primes (hS.bd x) (hS.bd y)
    (by simpa using lt_of_le_of_lt (le_max_right σ₀ 2) ht)).2.1]

end UpperTheory.ConvolutionTheory.Rs
