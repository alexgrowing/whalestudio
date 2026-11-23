import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PeriodLatticeCountable

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
  ReciprocityTheory.ChartRestriction.G.FD.FundamentalDomainTranslate ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeCountable
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}

theorem Data.fj_flow_real (X : Data E r) (la : Wt X.Ψ r) (ξ : Fin r → E) (hξ : X.IsIso ξ) (ν : X.Ψ → ℝ)
    (P : Frame X.Ψ r → ℂ) (hP : X.IsSec la P) (hbdd : ∃ C, ∀ x ∈ X.dom, X.pnorm la P x ≤ C)
    (x : Frame X.Ψ r) (hx : x ∈ X.dom) (s : X.Ψ → ℝ) :
    X.fj la ξ ν P (X.flow ξ (fun τ => (s τ : ℂ)) x) =
      cexp (4 * Real.pi * I * ∑ τ, (ν τ : ℂ) * s τ) * X.fj la ξ ν P x := by
  classical
  obtain ⟨hΛ, hξ0, -⟩ : ξ ∈ X.Λ ∧ herm X.Gm ξ ξ = 0 ∧ ξ ≠ 0 := hξ
  unfold Data.fj
  by_cases hc : ∀ p ∈ X.periods la, ∃ k : ℤ, 2 * ∑ τ, ν τ * p τ = k
  swap
  · rw [if_neg hc, if_neg hc, mul_zero]
  rw [if_pos hc, if_pos hc]
  by_cases hD : ∃ D : Set (X.Ψ → ℝ), MeasurableSet D ∧ IsAddFundamentalDomain (X.periods la) D volume ∧
      0 < volume D ∧ volume D < ⊤
  swap
  · rw [dif_neg hD, dif_neg hD, mul_zero]
  rw [dif_pos hD, dif_pos hD]
  have hFD : IsAddFundamentalDomain (X.periods la) hD.choose volume := hD.choose_spec.2.1

  set F : (X.Ψ → ℝ) → ℂ := fun t => P (X.flow ξ (fun τ => (t τ : ℂ)) x) *
    cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * t τ) with hF
  have hsum : ∀ a b : X.Ψ → ℝ, ∑ τ, (ν τ : ℂ) * (((a + b) τ : ℝ) : ℂ) =
      ∑ τ, (ν τ : ℂ) * a τ + ∑ τ, (ν τ : ℂ) * b τ := by
    intro a b
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [Pi.add_apply, Complex.ofReal_add]
    ring

  have hFper : ∀ p ∈ X.periods la, ∀ t, F (p + t) = F t := by
    intro p hp t
    simp only [hF]
    have hfl : (fun τ => (((p + t) τ : ℝ) : ℂ)) = cR X p + (fun τ => (t τ : ℂ)) := by
      funext τ
      simp only [cR, Pi.add_apply, Complex.ofReal_add]
    have hdom : X.flow ξ (fun τ => (t τ : ℂ)) x ∈ X.dom :=
      flow_real_mem_dom (X := X) hξ0 t x hx
    rw [hfl, ← flow_flow (X := X) hξ0, sec_periodic (X := X) la P hP hΛ hξ0 hp _ hdom]
    obtain ⟨k, hk⟩ := hc p hp
    have h1 : cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * p τ) = 1 := by
      have hk' : ∑ τ, (ν τ : ℂ) * p τ = (k : ℂ) / 2 := by
        have h2 := congrArg (fun y : ℝ => (y : ℂ)) hk
        push_cast at h2
        linear_combination h2 / 2
      rw [hk', show -(4 * Real.pi * I) * ((k : ℂ) / 2) = ((-k : ℤ) : ℂ) * (2 * Real.pi * I) by
        push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I (-k)
    rw [hsum p t, mul_add, Complex.exp_add, h1, one_mul]

  have hstep : ∀ t : X.Ψ → ℝ, P (X.flow ξ (fun τ => (t τ : ℂ)) (X.flow ξ (fun τ => (s τ : ℂ)) x)) *
      cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * t τ) =
      cexp (4 * Real.pi * I * ∑ τ, (ν τ : ℂ) * s τ) * F (s + t) := by
    intro t
    have hfl : (fun τ => (t τ : ℂ)) + (fun τ => (s τ : ℂ)) = fun τ => (((s + t) τ : ℝ) : ℂ) := by
      funext τ
      simp only [Pi.add_apply, Complex.ofReal_add]
      ring
    rw [flow_flow (X := X) hξ0, hfl]
    simp only [hF]
    rw [hsum s t]
    have he : cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * t τ) =
        cexp (4 * Real.pi * I * ∑ τ, (ν τ : ℂ) * s τ) *
          cexp (-(4 * Real.pi * I) * (∑ τ, (ν τ : ℂ) * s τ + ∑ τ, (ν τ : ℂ) * t τ)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    rw [he]
    ring
  have hint : ∫ t in hD.choose, P (X.flow ξ (fun τ => (t τ : ℂ)) (X.flow ξ (fun τ => (s τ : ℂ)) x)) *
      cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * t τ) =
      cexp (4 * Real.pi * I * ∑ τ, (ν τ : ℂ) * s τ) * ∫ t in hD.choose, F t := by
    simp_rw [hstep]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    exact fd_translate (X.periods la) hD.choose hFD F hFper s
  rw [hint]
  ring

end ReciprocityTheory.ChartRestriction.G.FD
