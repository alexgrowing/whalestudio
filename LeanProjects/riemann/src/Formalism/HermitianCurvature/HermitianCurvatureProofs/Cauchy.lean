import Formalism.HermitianCurvature.StatementE

namespace Formalism.FourierDecayAlt.P.Cauchy

open Complex Metric Set

theorem iteratedDeriv_ofReal {U : Set ℂ} (hU : IsOpen U) {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F U)
    {f : ℝ → ℝ} (hmem : ∀ x : ℝ, (x : ℂ) ∈ U) (hfF : ∀ x : ℝ, F x = f x) (p : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv p F) U ∧
      ∀ x : ℝ, iteratedDeriv p F x = (iteratedDeriv p f x : ℝ) := by
  induction p with
  | zero => simpa using ⟨hF, hfF⟩
  | succ p ih =>
    obtain ⟨hd, he⟩ := ih
    refine ⟨?_, fun x => ?_⟩
    · rw [iteratedDeriv_succ]
      exact hd.deriv hU
    · rw [iteratedDeriv_succ, iteratedDeriv_succ]
      have h0 : HasDerivAt (iteratedDeriv p F) (deriv (iteratedDeriv p F) x) (x : ℂ) :=
        (hd.differentiableAt (hU.mem_nhds (hmem x))).hasDerivAt
      have h1 : HasDerivAt (fun y : ℝ => (iteratedDeriv p F y).re)
          (deriv (iteratedDeriv p F) x).re x := h0.real_of_complex
      have h2 : (fun y : ℝ => (iteratedDeriv p F y).re) = iteratedDeriv p f := by
        funext y; rw [he y]; simp
      rw [h2] at h1
      have h3 : HasDerivAt (fun y : ℝ => iteratedDeriv p F y)
          (deriv (iteratedDeriv p F) x) x := h0.comp_ofReal
      have h4 : (fun y : ℝ => iteratedDeriv p F y) = fun y : ℝ => ((iteratedDeriv p f y : ℝ) : ℂ) := by
        funext y; rw [he y]
      rw [h4] at h3
      have h5 := h3.unique h1.ofReal_comp
      rw [h1.deriv]
      exact h5

theorem rpow_le_exp_one {σ : ℝ} (hσ : 4 ≤ σ) : (1 - 2 * (1 / (4 * σ))) ^ (-σ) ≤ Real.exp 1 := by
  have hσ0 : 0 < σ := by linarith
  have hx : 0 < 1 - 2 * (1 / (4 * σ)) := by
    have : 1 / (4 * σ) ≤ 1 / 16 := by
      apply one_div_le_one_div_of_le <;> linarith
    linarith
  rw [Real.rpow_def_of_pos hx]
  apply Real.exp_le_exp.mpr
  have h1 := Real.one_sub_inv_le_log_of_pos hx
  have h2 : (1 - 2 * (1 / (4 * σ)))⁻¹ = 2 * σ / (2 * σ - 1) := by
    have h21 : 1 - 2 * (1 / (4 * σ)) = (2 * σ - 1) / (2 * σ) := by
      field_simp
      ring
    rw [h21, inv_div]
  rw [h2] at h1
  have h3 : 1 - 2 * σ / (2 * σ - 1) = -(1 / (2 * σ - 1)) := by
    have : 2 * σ - 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [h3] at h1
  have h4 : 1 / (2 * σ - 1) ≤ 1 / σ := by
    apply one_div_le_one_div_of_le <;> linarith
  have h5 : -(1 / σ) ≤ Real.log (1 - 2 * (1 / (4 * σ))) := by linarith
  have h6 : σ * -(1 / σ) ≤ σ * Real.log (1 - 2 * (1 / (4 * σ))) :=
    mul_le_mul_of_nonneg_left h5 hσ0.le
  have h7 : σ * -(1 / σ) = -1 := by field_simp
  nlinarith

theorem base_bound {ε : ℝ} (hε : 0 < ε) (u : ℝ) {ρ : ℝ} (hρ : ρ ≤ 1 / 16) {w : ℂ}
    (hw : ‖w - u‖ ≤ ρ) :
    (1 + ε * Real.exp (-u)) * (1 - 2 * ρ) ≤ (1 + (ε : ℂ) * Complex.exp (-w)).re := by
  set a : ℝ := ε * Real.exp (-u) with ha
  have ha0 : 0 < a := by positivity
  have h1 : 1 + (ε : ℂ) * Complex.exp (-w) = ((1 + a : ℝ) : ℂ) + (a : ℂ) * (Complex.exp (-(w - u)) - 1) := by
    have : Complex.exp (-w) = Complex.exp (-(u : ℂ)) * Complex.exp (-(w - u)) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [this, ha]
    push_cast
    ring
  have h2 : ‖Complex.exp (-(w - u)) - 1‖ ≤ 2 * ρ := by
    have h := Complex.norm_exp_sub_one_le (x := -(w - u)) (by rw [norm_neg]; linarith)
    rw [norm_neg] at h
    linarith
  have h3 : -(2 * ρ) ≤ (Complex.exp (-(w - u)) - 1).re := by
    have := Complex.abs_re_le_norm (Complex.exp (-(w - u)) - 1)
    have := neg_abs_le (Complex.exp (-(w - u)) - 1).re
    linarith
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans hw
  have h4 : a * -(2 * ρ) ≤ a * (Complex.exp (-(w - u)) - 1).re :=
    mul_le_mul_of_nonneg_left h3 ha0.le
  rw [h1, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]
  nlinarith

end Formalism.FourierDecayAlt.P.Cauchy

namespace Formalism.FourierDecayAlt.P

open Complex Metric Set Formalism.FourierDecayAlt.P.Cauchy

theorem cauchy_theta_identity : Formalism.FourierDecayAlt.E.CauchyTheta := by
  intro σ ε hσ hε p u
  have hσ0 : 0 < σ := by linarith
  set ρ : ℝ := 1 / (4 * σ) with hρdef
  have hρ0 : 0 < ρ := by positivity
  have hρ : ρ ≤ 1 / 16 := by
    apply one_div_le_one_div_of_le <;> linarith
  set F : ℂ → ℂ := fun w => (1 + (ε : ℂ) * Complex.exp (-w)) ^ ((-σ : ℝ) : ℂ) with hF
  set f : ℝ → ℝ := fun v => (1 + ε * Real.exp (-v)) ^ (-σ) with hf
  set U : Set ℂ := {w | 0 < (1 + (ε : ℂ) * Complex.exp (-w)).re} with hUdef
  have hU : IsOpen U := by
    apply isOpen_lt continuous_const
    fun_prop
  have hFd : DifferentiableOn ℂ F U := by
    intro w hw
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.cpow_const (by fun_prop)
    exact Or.inl hw
  have hpos : ∀ x : ℝ, 0 < 1 + ε * Real.exp (-x) := fun x => by positivity
  have hcast : ∀ x : ℝ, 1 + (ε : ℂ) * Complex.exp (-(x : ℂ)) = ((1 + ε * Real.exp (-x) : ℝ) : ℂ) := by
    intro x; push_cast; ring
  have hmem : ∀ x : ℝ, (x : ℂ) ∈ U := by
    intro x
    show 0 < (1 + (ε : ℂ) * Complex.exp (-(x : ℂ))).re
    rw [hcast, Complex.ofReal_re]
    exact hpos x
  have hfF : ∀ x : ℝ, F x = f x := by
    intro x
    show (1 + (ε : ℂ) * Complex.exp (-(x : ℂ))) ^ ((-σ : ℝ) : ℂ) = _
    rw [hcast, ← Complex.ofReal_cpow (hpos x).le]
  have key := (iteratedDeriv_ofReal hU hFd hmem hfF p).2 u
  have hA : 0 < 1 + ε * Real.exp (-u) := hpos u
  have h12 : 0 < 1 - 2 * ρ := by linarith
  have hsub : closedBall (u : ℂ) ρ ⊆ U := by
    intro w hw
    have := base_bound hε u hρ (w := w) (by simpa [dist_eq_norm] using hw)
    have h0 : 0 < (1 + ε * Real.exp (-u)) * (1 - 2 * ρ) := by positivity
    exact lt_of_lt_of_le h0 this
  have hC : ∀ w ∈ sphere (u : ℂ) ρ, ‖F w‖ ≤ Real.exp 1 * (1 + ε * Real.exp (-u)) ^ (-σ) := by
    intro w hw
    have hb := base_bound hε u hρ (w := w) (by
      have : ‖w - u‖ = ρ := by simpa [dist_eq_norm] using hw
      exact this.le)
    have h0 : 0 < (1 + ε * Real.exp (-u)) * (1 - 2 * ρ) := by positivity
    have hn : (1 + ε * Real.exp (-u)) * (1 - 2 * ρ) ≤ ‖1 + (ε : ℂ) * Complex.exp (-w)‖ :=
      hb.trans (Complex.re_le_norm _)
    show ‖(1 + (ε : ℂ) * Complex.exp (-w)) ^ ((-σ : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_cpow_real]
    calc ‖1 + (ε : ℂ) * Complex.exp (-w)‖ ^ (-σ)
        ≤ ((1 + ε * Real.exp (-u)) * (1 - 2 * ρ)) ^ (-σ) :=
          Real.rpow_le_rpow_of_nonpos h0 hn (by linarith)
      _ = (1 + ε * Real.exp (-u)) ^ (-σ) * (1 - 2 * ρ) ^ (-σ) :=
          Real.mul_rpow hA.le h12.le
      _ ≤ (1 + ε * Real.exp (-u)) ^ (-σ) * Real.exp 1 :=
          mul_le_mul_of_nonneg_left (rpow_le_exp_one hσ) (by positivity)
      _ = _ := mul_comm _ _
  have hcau := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le p hρ0
    (hFd.diffContOnCl_ball hsub) hC
  rw [key, Complex.norm_real, Real.norm_eq_abs] at hcau
  refine hcau.trans (le_of_eq ?_)
  rw [hρdef, one_div, inv_pow, div_inv_eq_mul]
  ring

end Formalism.FourierDecayAlt.P
