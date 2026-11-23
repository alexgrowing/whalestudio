import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.AnalyticSeries.AnalyticAtTsum

noncomputable section

open scoped ComplexConjugate

namespace UpperTheory.ConvolutionTheory.Rs

open PositivityTheory.RgJS

theorem bdd {F : ℂ → ℂ} (hF : ∀ σ : ℝ, 0 < σ → AnalyticAt ℂ F σ) : ∃ M : ℝ, 0 < M ∧ ∀ σ : ℝ, 1 ≤ σ → σ ≤ 2 → ‖F σ‖ ≤ M := by
  have hc : ContinuousOn (fun t : ℝ => F t) (Set.Icc 1 2) := fun t ht =>
    ((hF t (by linarith [ht.1])).continuousAt.comp (f := fun t : ℝ => (t : ℂ)) Complex.continuous_ofReal.continuousAt).continuousWithinAt
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  exact ⟨max M 1, by positivity, fun σ h1 h2 => (hM σ ⟨h1, h2⟩).trans (le_max_left _ _)⟩

theorem bdd_zero {F : ℂ → ℂ} (hF : ∀ σ : ℝ, 0 < σ → AnalyticAt ℂ F σ) (h1 : F 1 = 0) :
    ∃ M : ℝ, 0 < M ∧ ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ‖F σ‖ ≤ M * (σ - 1) := by
  have hd : ∀ σ : ℝ, 0 < σ → AnalyticAt ℂ (dslope F 1) σ := fun σ hσ => by
    by_cases h : σ = 1
    · subst h
      obtain ⟨p, hp⟩ := hF 1 one_pos
      exact ⟨_, (by simpa using hp : HasFPowerSeriesAt F p 1).has_fpower_series_dslope_fslope⟩
    · have hne : (σ : ℂ) ≠ 1 := by exact_mod_cast h
      have : AnalyticAt ℂ (fun s => (s - 1)⁻¹ * (F s - F 1)) σ :=
        ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.2 hne)).mul ((hF σ hσ).sub analyticAt_const)
      refine this.congr ?_
      filter_upwards [dslope_eventuallyEq_slope_of_ne F hne] with s hs
      rw [hs, slope_def_field, div_eq_inv_mul]
  obtain ⟨M, hM, h⟩ := bdd hd
  refine ⟨M, hM, fun σ a b => ?_⟩
  have e := sub_smul_dslope F 1 (σ : ℂ)
  rw [h1, sub_zero, smul_eq_mul] at e
  have hn : ‖(σ : ℂ) - 1‖ = σ - 1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  rw [← e, norm_mul, hn, mul_comm]
  exact mul_le_mul_of_nonneg_right (h σ a.le b) (by linarith)

variable {W X : Type} {q : W → ℕ} {d : X → ℕ} {A : ∀ x, W → Fin (d x) → ℂ}

theorem norm_eq_re (hS : Sys q X d A) {ι : Type} [Fintype ι] (x : ι → X) (σ : ℝ) (hσ : 1 < σ) :
    ‖∑ i, ∑ j, ∑' p, lterm q (A (x i)) (A (x j)) σ p‖ = (∑ i, ∑ j, ∑' p, lterm q (A (x i)) (A (x j)) σ p).re := by
  have hq : ∀ w, (0 : ℝ) < q w := fun w => by
    have := hS.primes.two w
    exact_mod_cast (by omega : 0 < q w)
  have hs : ∀ i j, Summable fun p => lterm q (A (x i)) (A (x j)) σ p := fun i j =>
    ((conv1 W q X d A hS (x i) (x j)).1 σ hσ).of_norm
  have e : ∑ i, ∑ j, ∑' p, lterm q (A (x i)) (A (x j)) σ p =
      ((∑' p, DirichletSeriesUnbounded₂.cc A x p * Real.exp (-(DirichletSeriesUnbounded₂.ll q p * σ)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    simp_rw [← DirichletSeriesUnbounded₂.sum_lterm q A x hq σ]
    rw [Summable.tsum_finsetSum fun i _ => summable_sum (s := Finset.univ) fun j _ => hs i j]
    exact Finset.sum_congr rfl fun i _ => (Summable.tsum_finsetSum fun j _ => hs i j).symm
  rw [e, Complex.norm_real, Complex.ofReal_re,
    Real.norm_of_nonneg (tsum_nonneg fun p => mul_nonneg (DirichletSeriesUnbounded₂.cc_nonneg A x p) (Real.exp_pos _).le)]

theorem re_swap (x y : X) (σ : ℝ) :
    (∑' p, lterm q (A y) (A x) σ p).re = (∑' p, lterm q (A x) (A y) σ p).re := by
  rw [← Complex.conj_re, Complex.conj_tsum]
  refine congrArg _ (tsum_congr fun p => ?_)
  have h : conj ((q p.1 : ℂ) ^ (-(σ : ℂ))) = (q p.1 : ℂ) ^ (-(σ : ℂ)) := by
    rw [Common0Aux.cpow_real, Complex.conj_ofReal]
  simp only [lterm, map_div₀, map_mul, map_pow, h, Complex.conj_conj, map_add, map_natCast, map_one]
  ring

open Classical in

theorem exp_re (hS : Sys q X d A) (x y : X) (F : ℂ → ℂ) (σ₀ : ℝ) (hF : ∀ σ : ℝ, 0 < σ → AnalyticAt ℂ F σ)
    (he : ∀ σ : ℝ, σ₀ < σ → F σ = (if x = y then (σ : ℂ) - 1 else 1) * eul q (A x) (A y) σ) (σ : ℝ) (hσ : 1 < σ) :
    ‖F σ‖ = (if x = y then σ - 1 else 1) * Real.exp (∑' p, lterm q (A x) (A y) σ p).re := by
  rw [eq_exp hS x y F (fun s => if x = y then s - 1 else 1) σ₀ hF (fun t => by
    split_ifs
    · exact analyticAt_id.sub analyticAt_const
    · exact analyticAt_const) he σ hσ, norm_mul, Complex.norm_exp]
  split_ifs
  · rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  · rw [norm_one]

open Classical in

theorem ne_zero_one (hS : Sys q X d A) (x y : X) (F : ℂ → ℂ) (σ₀ : ℝ) (hF : ∀ σ : ℝ, 0 < σ → AnalyticAt ℂ F σ)
    (he : ∀ σ : ℝ, σ₀ < σ → F σ = (if x = y then (σ : ℂ) - 1 else 1) * eul q (A x) (A y) σ) : F 1 ≠ 0 := by
  intro h0
  obtain ⟨M, hM, hb⟩ := bdd_zero hF h0
  by_cases hxy : x = y
  · subst hxy
    refine unb W q X d A hS Unit (fun _ => x) ⟨Real.log M, fun σ h1 h2 => ?_⟩
    rw [norm_eq_re hS _ σ h1]
    have h := hb σ h1 h2
    rw [exp_re hS x x F σ₀ hF he σ h1, if_pos rfl, mul_comm] at h
    simpa using (Real.le_log_iff_exp_le hM).2 (le_of_mul_le_mul_right h (by linarith))
  · obtain ⟨G, σ₁, hG, hGe⟩ := hS.rs x x
    obtain ⟨H, σ₂, hH, hHe⟩ := hS.rs y y
    obtain ⟨M₁, hM₁, b₁⟩ := bdd hG
    obtain ⟨M₂, hM₂, b₂⟩ := bdd hH
    refine unb W q X d A hS Bool (fun b => cond b x y) ⟨Real.log (M₁ * M₂ * M * M), fun σ h1 h2 => ?_⟩
    rw [norm_eq_re hS _ σ h1]
    have h := hb σ h1 h2
    have g₁ := b₁ σ h1.le h2
    have g₂ := b₂ σ h1.le h2
    rw [exp_re hS x y F σ₀ hF he σ h1, if_neg hxy, one_mul] at h
    rw [exp_re hS x x G σ₁ hG hGe σ h1, if_pos rfl] at g₁
    rw [exp_re hS y y H σ₂ hH hHe σ h1, if_pos rfl] at g₂
    refine (Real.le_log_iff_exp_le (by positivity)).2 ?_
    simp only [Fintype.sum_bool, cond_true, cond_false, Complex.add_re, re_swap (A := A) x y σ, Real.exp_add]
    set a := Real.exp (∑' p, lterm q (A x) (A x) σ p).re
    set b := Real.exp (∑' p, lterm q (A y) (A y) σ p).re
    set c := Real.exp (∑' p, lterm q (A x) (A y) σ p).re
    have ha : 0 < a := Real.exp_pos _
    have hb' : 0 < b := Real.exp_pos _
    have hc : 0 < c := Real.exp_pos _
    have ht : 0 < σ - 1 := by linarith
    calc a * c * (c * b) = a * b * c * c := by ring
      _ ≤ a * b * (M * (σ - 1)) * (M * (σ - 1)) := by gcongr
      _ = ((σ - 1) * a) * ((σ - 1) * b) * M * M := by ring
      _ ≤ M₁ * M₂ * M * M := by gcongr

end UpperTheory.ConvolutionTheory.Rs
