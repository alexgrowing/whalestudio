import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.LUnH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteDimensionalLev
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.Kd.K4 Polynomial
open scoped Matrix MatrixGroups

namespace UpperTheory.Kd.K4.BoundedOrderUnits

open Filter Topology

private theorem near_one {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (φ : ℂ → ℂ)
    (hφ : X.an X.jK = (φ : Mero)) (hφc : ContinuousOn φ Hs) :
    ∃ t : ℝ, 0 < t ∧ ∀ z : ℂ, t < z.im → ‖Complex.exp (2 * Real.pi * Complex.I * z) * φ z - 1‖ ≤ 1 / 2 := by
  obtain ⟨φ', C, hφ', hsum⟩ := X.an_exp X.jK
  have hinj : Function.Injective (fun n : ℕ => (n : ℚ) - 1) := fun a b h => by simpa using h
  have hsumN : ∀ z : ℂ, C < z.im → HasSum (fun n : ℕ => ε ((X.exp X.jK).coeff ((n : ℚ) - 1)) *
      Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * z)) (Complex.exp (2 * Real.pi * Complex.I * z) * φ' z) := by
    intro z hz
    have h1 := hsum z hz
    rw [← hinj.hasSum_iff] at h1
    · have h2 := h1.mul_left (Complex.exp (2 * Real.pi * Complex.I * z))
      have e : (fun n : ℕ => ε ((X.exp X.jK).coeff ((n : ℚ) - 1)) *
          Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * z)) = fun n : ℕ =>
          Complex.exp (2 * Real.pi * Complex.I * z) * (ε ((X.exp X.jK).coeff ((n : ℚ) - 1)) *
            Complex.exp (2 * Real.pi * Complex.I * (((n : ℚ) - 1 : ℚ) : ℂ) * z)) := by
        funext n
        rw [mul_left_comm, ← Complex.exp_add]
        congr 2
        push_cast
        ring
      rw [e]
      exact h2
    · intro r hr
      have : (X.exp X.jK).coeff r = 0 := by
        by_contra hne
        obtain ⟨m, rfl⟩ := GlobalTheory.K4.LevFin.exponent_int X X.jK (X.j_inv _) r hne
        have hm : -1 ≤ m := by
          by_contra hm
          exact hne (X.j_exp.2.1 _ (by exact_mod_cast (not_le.1 hm)))
        refine hr ⟨(m + 1).toNat, ?_⟩
        show (((m + 1).toNat : ℕ) : ℚ) - 1 = m
        rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
        push_cast
        ring
      simp [this]
  obtain ⟨B, t, hB⟩ := GlobalTheory.KZ.ExpBound.series_bound _ _ C hsumN
  simp only [Nat.cast_zero, zero_sub, X.j_exp.1, map_one] at hB
  have ht : Tendsto (fun s : ℝ => B * Real.exp (-(2 * Real.pi * (s - t)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => 2 * Real.pi * (s - t)) atTop atTop := by
      apply Tendsto.const_mul_atTop Real.two_pi_pos
      exact tendsto_atTop_add_const_right _ _ tendsto_id
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul B
  obtain ⟨s, hs⟩ := eventually_atTop.1 (ht.eventually (ge_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)))
  refine ⟨max (max s t) 1, lt_max_of_lt_right one_pos, fun z hz => ?_⟩
  have hzH : z ∈ Hs := lt_trans (lt_max_of_lt_right one_pos) hz
  have hev : φ =ᶠ[codiscreteWithin Hs] φ' := Filter.Germ.coe_eq.mp (hφ.symm.trans hφ')
  have h1 := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hev z hzH
  have hHs : Hs ∈ 𝓝 z := SiegelModel.isOpen_Hs.mem_nhds hzH
  have h2 : Hs ∈ 𝓝[≠] z := mem_nhdsWithin_of_mem_nhds hHs
  have h3 : {w : ℂ | max (max s t) 1 < w.im} ∈ 𝓝[≠] z :=
    mem_nhdsWithin_of_mem_nhds ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz)
  have hc : ContinuousAt (fun w => ‖Complex.exp (2 * Real.pi * Complex.I * w) * φ w - 1‖) z := by
    have := hφc.continuousAt hHs
    fun_prop
  refine le_of_tendsto (hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {z}ᶜ))) ?_
  filter_upwards [h1, h2, h3] with w hw1 hw2 hw3
  rcases hw1 with e | e
  · have e' : φ w = φ' w := e
    rw [e']
    simp only [Set.mem_setOf_eq, max_lt_iff] at hw3
    exact (hB w hw3.1.2).trans (hs _ hw3.1.1.le)
  · exact absurd hw2 e

private theorem deriv_ne (φ : ℂ → ℂ) (hd : DifferentiableOn ℂ φ Hs) (t : ℝ) (ht : 0 < t)
    (h : ∀ z : ℂ, t < z.im → ‖Complex.exp (2 * Real.pi * Complex.I * z) * φ z - 1‖ ≤ 1 / 2)
    (z : ℂ) (hz : t + 1 < z.im) : deriv φ z ≠ 0 := by
  intro h0
  have hsub : ∀ w ∈ Metric.closedBall z 1, t < w.im := by
    intro w hw
    have h1 : ‖w - z‖ ≤ 1 := by simpa [dist_eq_norm] using hw
    have h2 := (Complex.abs_im_le_norm (w - z)).trans h1
    rw [Complex.sub_im, abs_le] at h2
    linarith [h2.1]
  have hG : DifferentiableOn ℂ (fun w => Complex.exp (2 * Real.pi * Complex.I * w) * φ w - 1) Hs :=
    (DifferentiableOn.mul (by fun_prop) hd).sub_const 1
  have hb := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := z) (R := 1) (C := 1 / 2) one_pos
    (hG.diffContOnCl_ball (fun w hw => lt_trans ht (hsub w hw)))
    (fun w hw => h w (hsub w (Metric.sphere_subset_closedBall hw)))
  have hzH : z ∈ Hs := show 0 < z.im by linarith
  have hφ : HasDerivAt φ 0 z := h0 ▸ (hd.differentiableAt (SiegelModel.isOpen_Hs.mem_nhds hzH)).hasDerivAt
  have he : HasDerivAt (fun w : ℂ => Complex.exp (2 * Real.pi * Complex.I * w))
      (Complex.exp (2 * Real.pi * Complex.I * z) * (2 * Real.pi * Complex.I)) z := by
    simpa using ((hasDerivAt_id z).const_mul (2 * Real.pi * Complex.I : ℂ)).cexp
  have hD : HasDerivAt (fun w => Complex.exp (2 * Real.pi * Complex.I * w) * φ w - 1) _ z := (he.mul hφ).sub_const 1
  rw [hD.deriv, mul_zero, add_zero, mul_right_comm, norm_mul] at hb
  have h1 := h z (by linarith)
  have h2 := norm_sub_norm_le (1 : ℂ) (Complex.exp (2 * Real.pi * Complex.I * z) * φ z)
  rw [norm_one, norm_sub_rev] at h2
  have h3 : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by simp [abs_of_pos Real.pi_pos]
  rw [h3] at hb
  nlinarith [Real.pi_gt_three]

private theorem onto (φ : ℂ → ℂ) (hd : DifferentiableOn ℂ φ Hs)
    (hinv : ∀ γ : SL(2, ℤ), ∀ z ∈ Hs, φ (mob (ofSL γ) z) = φ z) (t : ℝ) (ht : 0 < t)
    (h : ∀ z : ℂ, t < z.im → ‖Complex.exp (2 * Real.pi * Complex.I * z) * φ z - 1‖ ≤ 1 / 2)
    (a : ℂ) : ∃ τ ∈ Hs, φ τ = a := by
  by_contra hc
  push Not at hc
  have hne : ∀ τ ∈ Hs, φ τ - a ≠ 0 := fun τ hτ => sub_ne_zero.2 (hc τ hτ)
  obtain ⟨c, hcc⟩ := GlobalTheory.T.const_of_slTwoInt_invariant_bounded_upperHalfPlane (fun w => (φ w - a)⁻¹) ((hd.sub_const a).inv hne)
    (fun γ z hz => by simp only [hinv γ z hz]) ⟨1, max t (‖a‖ + 1), fun z hz hzt => by
      rw [max_lt_iff] at hzt
      have h1 := h z hzt.1
      have h2 := norm_sub_norm_le (1 : ℂ) (Complex.exp (2 * Real.pi * Complex.I * z) * φ z)
      rw [norm_one, norm_sub_rev, norm_mul, Complex.norm_exp] at h2
      have e : (2 * Real.pi * Complex.I * z : ℂ).re = -(2 * Real.pi * z.im) := by
        simp [Complex.mul_re, Complex.mul_im]
      rw [e, Real.exp_neg] at h2
      have h3 := Real.add_one_le_exp (2 * Real.pi * z.im)
      have h4 := Real.exp_pos (2 * Real.pi * z.im)
      have h5 : 1 / 2 * Real.exp (2 * Real.pi * z.im) ≤ ‖φ z‖ := by
        rw [← le_div_iff₀ h4, div_eq_inv_mul ‖φ z‖]; linarith
      have h6 := norm_sub_norm_le (φ z) a
      have h7 : 0 < z.im := hz
      rw [norm_inv]
      apply inv_le_one_of_one_le₀
      nlinarith [Real.pi_gt_three]⟩
  have hzH : ((t + 2 : ℝ) : ℂ) * Complex.I ∈ Hs := by simp [Hs]; linarith
  refine deriv_ne φ hd t ht h (((t + 2 : ℝ) : ℂ) * Complex.I) (by simp) ?_
  have hev : φ =ᶠ[𝓝 (((t + 2 : ℝ) : ℂ) * Complex.I)] fun _ => c⁻¹ + a := by
    filter_upwards [SiegelModel.isOpen_Hs.mem_nhds hzH] with w hw
    rw [← hcc w hw]
    simp
  rw [hev.deriv_eq, deriv_const]

private theorem bdd_order (g : ℂ → ℂ) (hg : AnalyticOnNhd ℂ g Hs) (z0 : ℂ) (hz0 : z0 ∈ Hs) (h0 : g z0 ≠ 0)
    (K : Set ℂ) (hK : IsCompact K) (hKH : K ⊆ Hs) : ∃ E : ℕ, ∀ τ ∈ K, analyticOrderAt g τ ≤ E := by
  refine hK.induction_on (p := fun S => ∃ E : ℕ, ∀ τ ∈ S, analyticOrderAt g τ ≤ E) ⟨0, by simp⟩ ?_ ?_ ?_
  · rintro s u hsu ⟨E, hE⟩
    exact ⟨E, fun τ hτ => hE τ (hsu hτ)⟩
  · rintro s u ⟨E, hE⟩ ⟨F, hF⟩
    refine ⟨max E F, ?_⟩
    rintro τ (hτ | hτ)
    · exact (hE τ hτ).trans (by exact_mod_cast le_max_left _ _)
    · exact (hF τ hτ).trans (by exact_mod_cast le_max_right _ _)
  · intro x hx
    have hnz : ¬ ∀ᶠ w in 𝓝 x, g w = 0 := fun hz =>
      h0 (hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero GlobalTheory.FN.isPreconnected_Hs (hKH hx) hz hz0)
    have hne := (hg x (hKH hx)).eventually_eq_zero_or_eventually_ne_zero.resolve_left hnz
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (fun h => hnz (analyticOrderAt_eq_top.1 h))
    rw [eventually_nhdsWithin_iff] at hne
    refine ⟨_, mem_nhdsWithin_of_mem_nhds hne, n, fun τ hτ => ?_⟩
    by_cases e : τ = x
    · rw [e, hn]
    · rw [analyticOrderAt_eq_zero.2 (Or.inr (hτ e))]
      exact zero_le

private theorem order_inv (φ : ℂ → ℂ)
    (hinv : ∀ γ : SL(2, ℤ), ∀ z ∈ Hs, φ (mob (ofSL γ) z) = φ z) (γ : SL(2, ℤ)) (τ : ℂ) (hτ : τ ∈ Hs) :
    analyticOrderAt (fun s => φ s - φ τ) τ =
      analyticOrderAt (fun s => φ s - φ (mob (ofSL γ) τ)) (mob (ofSL γ) τ) := by
  have hden := GlobalTheory.KZ.InvFun.mob_ofSL_den_ne_zero γ hτ
  have han : AnalyticAt ℂ (mob (ofSL γ)) τ := by
    unfold mob
    exact AnalyticAt.div (by fun_prop) (by fun_prop) hden
  have hdet : (ent (ofSL γ) 0 0 : ℂ) * ent (ofSL γ) 1 1 - ent (ofSL γ) 0 1 * ent (ofSL γ) 1 0 = 1 := by
    have he : ∀ i j, ent (ofSL γ) i j = ((γ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℚ) := fun _ _ => rfl
    have h1 := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at h1
    simp only [he]
    exact_mod_cast h1
  have hD : HasDerivAt (mob (ofSL γ)) _ τ :=
    (((hasDerivAt_id τ).const_mul (ent (ofSL γ) 0 0 : ℂ)).add_const (ent (ofSL γ) 0 1 : ℂ)).div
      (((hasDerivAt_id τ).const_mul (ent (ofSL γ) 1 0 : ℂ)).add_const (ent (ofSL γ) 1 1 : ℂ)) hden
  have hD0 : deriv (mob (ofSL γ)) τ ≠ 0 := by
    rw [hD.deriv]
    refine div_ne_zero ?_ (pow_ne_zero _ hden)
    simp only [id]
    intro h
    apply one_ne_zero (α := ℂ)
    rw [← hdet, ← h]
    ring
  rw [← analyticOrderAt_comp_of_deriv_ne_zero han hD0]
  apply analyticOrderAt_congr
  filter_upwards [SiegelModel.isOpen_Hs.mem_nhds hτ] with w hw
  simp only [Function.comp_apply, hinv γ w hw, hinv γ τ hτ]

end UpperTheory.Kd.K4.BoundedOrderUnits

open UpperTheory.Kd.K4.BoundedOrderUnits in
theorem UpperTheory.Kd.K4.jan :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∃ (φ : ℂ → ℂ) (E : ℕ), X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs ∧ (∀ z : ℂ, ∃ τ ∈ Hs, φ τ = z) ∧
      ∀ τ ∈ Hs, analyticOrderAt (fun s => φ s - φ τ) τ ≤ E := by
  intro Ω _ _ _ ε X
  obtain ⟨φ, hφ, hd⟩ := X.j_hol
  have hinv := GlobalTheory.T.modularTower_function_slTwoInt_invariant X X.jK φ hd.continuousOn hφ X.j_inv
  obtain ⟨t, ht, h⟩ := near_one X φ hφ hd.continuousOn
  have hne := deriv_ne φ hd t ht h
  have han := hd.analyticOnNhd SiegelModel.isOpen_Hs
  obtain ⟨E, hE⟩ := bdd_order (deriv φ) han.deriv (((t + 2 : ℝ) : ℂ) * Complex.I) (by simp [Hs]; linarith)
    (hne _ (by simp)) (Set.Icc (-1) 1 ×ℂ Set.Icc (1 / 2) (t + 1)) (isCompact_Icc.reProdIm isCompact_Icc)
    (fun z hz => lt_of_lt_of_le (by norm_num) hz.2.1)
  refine ⟨φ, E + 1, hφ, hd, onto φ hd hinv t ht h, fun τ hτ => ?_⟩
  obtain ⟨γ, hγ⟩ := ModularGroup.exists_smul_mem_fd ⟨τ, hτ⟩
  have hm : mob (ofSL γ) τ = ((γ • (⟨τ, hτ⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) :=
    SiegelModel.mob_ofSL γ ⟨τ, hτ⟩
  rw [order_inv φ hinv γ τ hτ, hm]
  generalize γ • (⟨τ, hτ⟩ : UpperHalfPlane) = σ at hγ
  rw [← (han σ σ.2).analyticOrderAt_deriv_add_one]
  push_cast
  gcongr
  by_cases hσ : t + 1 < (σ : ℂ).im
  · rw [analyticOrderAt_eq_zero.2 (Or.inr (hne _ hσ))]
    exact zero_le
  · have h1 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hγ
    have h2 := abs_le.1 hγ.2
    have h3 := σ.im_pos
    refine hE _ ⟨⟨?_, ?_⟩, ?_, not_lt.1 hσ⟩
    · show -1 ≤ σ.re
      linarith [h2.1]
    · show σ.re ≤ 1
      linarith [h2.2]
    · show 1 / 2 ≤ σ.im
      nlinarith
