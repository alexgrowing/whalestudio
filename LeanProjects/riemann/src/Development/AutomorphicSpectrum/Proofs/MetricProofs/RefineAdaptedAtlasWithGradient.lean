import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.RegGlue
import ReciprocityTheory.AnalyticForms.LeviForms.RegChartC
import ReciprocityTheory.AnalyticForms.LeviForms.TailCut
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

noncomputable section

theorem rLoc_rescale_bound {e : ℕ} (S : Finset (Fin e)) (m : Fin e → ℕ) (z₀ : Fin e → ℂ) (ρ : ℝ)
    (hρ : 0 < ρ) (hρ8 : ρ ≤ 1 / 8) (hz₀ : ‖z₀‖ < 1) (hfar : ∀ i, z₀ i ≠ 0 → 3 * ρ < ‖z₀ i‖) :
    ∃ c : ℝ, ∀ w ∈ closedBall (0 : Fin e → ℂ) 2, (∀ i ∈ S, z₀ i = 0 → w i ≠ 0) →
      |rLoc S m ((ρ : ℂ) • w + z₀) - rLoc (S.filter (fun i => z₀ i = 0)) m w| ≤ c := by
  classical
  set K : ℝ := Real.log (4 / ρ ^ 2) with hK
  refine ⟨∑ i ∈ S, (m i : ℝ) * K, fun w hw hne => ?_⟩
  have hw' : ∀ i, ‖w i‖ ≤ 2 := fun i =>
    (norm_le_pi_norm w i).trans (by simpa using hw)
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hone : (1 : ℝ) ≤ 1 / ρ ^ 2 := by
    rw [le_div_iff₀ hρ2]; nlinarith
  have hlog1 : Real.log (1 / ρ ^ 2) ≤ K :=
    Real.log_le_log (by positivity) (by
      apply div_le_div_of_nonneg_right (by norm_num) hρ2.le)
  have hlog0 : 0 ≤ Real.log (1 / ρ ^ 2) := Real.log_nonneg hone
  have hterm : ∀ i ∈ S, |(m i : ℝ) * Real.log (4 / ‖((ρ : ℂ) • w + z₀) i‖ ^ 2) -
      (if z₀ i = 0 then (m i : ℝ) * Real.log (4 / ‖w i‖ ^ 2) else 0)| ≤ (m i : ℝ) * K := by
    intro i hi
    have hm0 : (0 : ℝ) ≤ m i := Nat.cast_nonneg _
    have hzi : ((ρ : ℂ) • w + z₀) i = (ρ : ℂ) * w i + z₀ i := by simp
    by_cases h0 : z₀ i = 0
    · have hwi : ‖w i‖ ≠ 0 := norm_ne_zero_iff.2 (hne i hi h0)
      have hwp : 0 < ‖w i‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hwi)
      have hn : ‖((ρ : ℂ) • w + z₀) i‖ = ρ * ‖w i‖ := by
        rw [hzi, h0, add_zero, norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ.le]
      have hsplit : Real.log (4 / (ρ * ‖w i‖) ^ 2) =
          Real.log (4 / ‖w i‖ ^ 2) + Real.log (1 / ρ ^ 2) := by
        rw [← Real.log_mul (by positivity) (by positivity)]
        congr 1
        field_simp
      rw [if_pos h0, hn, hsplit, mul_add, add_sub_cancel_left, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left hlog1 hm0
    · have hfi := hfar i h0
      have hz1 : ‖z₀ i‖ < 1 := (norm_le_pi_norm z₀ i).trans_lt hz₀
      have hρw : ‖(ρ : ℂ) * w i‖ ≤ 2 * ρ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ.le]
        nlinarith [hw' i]
      have hlo : ρ ≤ ‖((ρ : ℂ) • w + z₀) i‖ := by
        rw [hzi]
        have h3 := norm_sub_le ((ρ : ℂ) * w i + z₀ i) ((ρ : ℂ) * w i)
        rw [add_sub_cancel_left] at h3
        linarith
      have hhi : ‖((ρ : ℂ) • w + z₀) i‖ ≤ 2 := by
        rw [hzi]
        have := norm_add_le ((ρ : ℂ) * w i) (z₀ i)
        linarith
      set t := ‖((ρ : ℂ) • w + z₀) i‖ with ht
      have ht0 : 0 < t := lt_of_lt_of_le hρ hlo
      have ht2 : 0 < t ^ 2 := by positivity
      have hA : 0 ≤ Real.log (4 / t ^ 2) := by
        apply Real.log_nonneg
        rw [le_div_iff₀ ht2]; nlinarith
      have hB : Real.log (4 / t ^ 2) ≤ K := by
        apply Real.log_le_log (by positivity)
        apply div_le_div_of_nonneg_left (by norm_num) hρ2
        nlinarith
      rw [if_neg h0, sub_zero, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left hB hm0
  have hdiff : rLoc S m ((ρ : ℂ) • w + z₀) - rLoc (S.filter (fun i => z₀ i = 0)) m w =
      ∑ i ∈ S, ((m i : ℝ) * Real.log (4 / ‖((ρ : ℂ) • w + z₀) i‖ ^ 2) -
        (if z₀ i = 0 then (m i : ℝ) * Real.log (4 / ‖w i‖ ^ 2) else 0)) := by
    unfold rLoc
    rw [Finset.sum_filter, add_sub_add_left_eq_sub, Finset.sum_sub_distrib]
  rw [hdiff]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)

theorem fderiv_rescale_norm_le {e : ℕ} (f : (Fin e → ℂ) → ℝ) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (z₀ w : Fin e → ℂ) :
    ‖fderiv ℝ (fun w => f ((ρ : ℂ) • w + z₀)) w‖ ≤ ‖fderiv ℝ f ((ρ : ℂ) • w + z₀)‖ := by
  have hne : ρ ≠ 0 := hρ.ne'
  let I : (Fin e → ℂ) ≃L[ℝ] (Fin e → ℂ) := ContinuousLinearEquiv.equivOfInverse
    (ρ • ContinuousLinearMap.id ℝ (Fin e → ℂ)) (ρ⁻¹ • ContinuousLinearMap.id ℝ (Fin e → ℂ))
    (fun x => by simp [smul_smul, hne]) (fun x => by simp [smul_smul, hne])
  have hI : ∀ u, I u = (ρ : ℂ) • u := by
    intro u
    ext i
    simp [I]
  have hfun : (fun w => f ((ρ : ℂ) • w + z₀)) = (fun u => f (u + z₀)) ∘ I := by
    funext u
    simp [hI]
  rw [hfun, I.comp_right_fderiv, fderiv_comp_add_right, hI]
  have hIn : ‖((I : (Fin e → ℂ) ≃L[ℝ] (Fin e → ℂ)) : (Fin e → ℂ) →L[ℝ] (Fin e → ℂ))‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => ?_
    have : ((I : (Fin e → ℂ) ≃L[ℝ] (Fin e → ℂ)) : (Fin e → ℂ) →L[ℝ] (Fin e → ℂ)) u = (ρ : ℂ) • u := hI u
    rw [this, norm_smul, Complex.norm_real, Real.norm_of_nonneg hρ.le]
    nlinarith [norm_nonneg u]
  calc _ ≤ ‖fderiv ℝ f ((ρ : ℂ) • w + z₀)‖ * ‖((I : (Fin e → ℂ) ≃L[ℝ] (Fin e → ℂ)) : (Fin e → ℂ) →L[ℝ] (Fin e → ℂ))‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ _ := by nlinarith [norm_nonneg (fderiv ℝ f ((ρ : ℂ) • w + z₀))]

theorem refine_local_chart {e : ℕ} {X : Type} [TopologicalSpace X] (A B : FinHolAtlas e X)
    (L th : LocPot X) (s : X → X → ℂ) (ph : X → ℝ) (C₅ M : ℝ)
    (hle : ∀ y, logNormSec L s y ≤ 0) (hAB : A.Compatible B)
    (h2 : ∀ j, closedBall (0 : Fin e → ℂ) 2 ⊆ (B.chart j).target)
    (hM : ∀ j, ∃ (S : Finset (Fin e)) (m : Fin e → ℕ), (∀ i ∈ S, 1 ≤ m i) ∧
      (∀ y ∈ (B.chart j).target, ((B.chart j).symm y ∈ bdry s ↔ ∃ i ∈ S, y i = 0)) ∧
      ∀ y ∈ closedBall (0 : Fin e → ℂ) 2, (B.chart j).symm y ∉ bdry s →
        |rW L s ((B.chart j).symm y) - rLoc S m y| ≤ M)
    (hG : IsGradBound B L s ph C₅) (j : Fin B.n) (x : X) (hx : x ∈ (B.chart j).source)
    (hx1 : B.chart j x ∈ ball (0 : Fin e → ℂ) 1) :
    ∃ ψ : OpenPartialHomeomorph X (Fin e → ℂ), (IsCompatChart A ψ ∧
      closedBall (0 : Fin e → ℂ) 2 ⊆ ψ.target ∧
      (∃ M' : ℝ, ∃ (S : Finset (Fin e)) (m : Fin e → ℕ), (∀ i ∈ S, 1 ≤ m i) ∧
        (∀ y ∈ ψ.target, (ψ.symm y ∈ bdry s ↔ ∃ i ∈ S, y i = 0)) ∧
        ∀ y ∈ closedBall (0 : Fin e → ℂ) 2, ψ.symm y ∉ bdry s →
          |rW L s (ψ.symm y) - rLoc S m y| ≤ M') ∧
      (∀ y ∈ ball (0 : Fin e → ℂ) (3 / 2), ψ.symm y ∉ bdry s →
        ‖fderiv ℝ (ph ∘ ψ.symm) y‖ ≤
          |C₅| * rW L s (ψ.symm y) ^ |C₅| * Real.exp (rW L s (ψ.symm y) / 2))) ∧
      x ∈ ψ.source ∧ ψ x ∈ ball (0 : Fin e → ℂ) 1 ∧ ψ.source ⊆ th.U x := by
  classical
  set c := B.chart j with hc
  set z₀ : Fin e → ℂ := c x with hz₀
  have hz₀1 : ‖z₀‖ < 1 := by simpa using hx1
  obtain ⟨S, m, hm, hb, hr⟩ := hM j
  have hOopen : IsOpen (c.target ∩ c.symm ⁻¹' th.U x) :=
    c.continuousOn_symm.isOpen_inter_preimage c.open_target (th.isOpen_U x)
  have hz₀O : z₀ ∈ c.target ∩ c.symm ⁻¹' th.U x :=
    ⟨c.map_source hx, by
      show c.symm (c x) ∈ th.U x
      rw [c.left_inv hx]; exact th.mem_U x⟩
  obtain ⟨r, hr0, hrO⟩ := Metric.isOpen_iff.1 hOopen z₀ hz₀O
  obtain ⟨ρ, hρ0, hρ8, hρr, hfar⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 8 ∧ 3 * ρ ≤ r ∧
      ∀ i, z₀ i ≠ 0 → 3 * ρ < ‖z₀ i‖ := by
    have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ i, z₀ i ≠ 0 → 3 * ρ < ‖z₀ i‖ := by
      refine Filter.eventually_all.2 fun i => ?_
      by_cases h : z₀ i = 0
      · exact Filter.Eventually.of_forall fun _ h' => absurd h h'
      · have hp : 0 < ‖z₀ i‖ / 3 := by
          have := norm_pos_iff.2 h
          positivity
        filter_upwards [Ioo_mem_nhdsGT hp] with ρ hρ _
        have := hρ.2
        linarith
    have h1 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ ∈ Set.Ioo (0 : ℝ) (min (1 / 8) (r / 3)) :=
      Ioo_mem_nhdsGT (lt_min (by norm_num) (by positivity))
    obtain ⟨ρ, hρ, hev'⟩ := (h1.and hev).exists
    have ha := lt_of_lt_of_le hρ.2 (min_le_left _ _)
    have hb' := lt_of_lt_of_le hρ.2 (min_le_right _ _)
    exact ⟨ρ, hρ.1, ha.le, by linarith, hev'⟩
  have hs : IsOpen (c.source ∩ c ⁻¹' ball z₀ (3 * ρ)) :=
    c.continuousOn.isOpen_inter_preimage c.open_source Metric.isOpen_ball
  have hρC : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ0.ne'
  have ha : ((ρ : ℂ))⁻¹ ≠ 0 := inv_ne_zero hρC
  set ψ : OpenPartialHomeomorph X (Fin e → ℂ) :=
    (c.restrOpen _ hs).transHomeomorph (pa_aff ((ρ : ℂ))⁻¹ ha z₀) with hψ
  have hinv : ∀ w, (pa_aff ((ρ : ℂ))⁻¹ ha z₀).symm w = (ρ : ℂ) • w + z₀ := by
    intro w
    show (((ρ : ℂ))⁻¹)⁻¹ • w + z₀ = _
    rw [inv_inv]
  have hsymm : ∀ w, ψ.symm w = c.symm ((ρ : ℂ) • w + z₀) := by
    intro w
    show c.symm ((pa_aff ((ρ : ℂ))⁻¹ ha z₀).symm w) = _
    rw [hinv]
  have hnorm : ∀ w : Fin e → ℂ, ‖(ρ : ℂ) • w‖ = ρ * ‖w‖ := by
    intro w
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hρ0.le]
  have hdist : ∀ w : Fin e → ℂ, ‖(ρ : ℂ) • w + z₀ - z₀‖ = ρ * ‖w‖ := by
    intro w
    rw [add_sub_cancel_right, hnorm]

  have htar1 : ∀ w : Fin e → ℂ, ‖w‖ < 3 → w ∈ ψ.target := by
    intro w hw
    have hzb : (ρ : ℂ) • w + z₀ ∈ ball z₀ (3 * ρ) := by
      rw [Metric.mem_ball, dist_eq_norm, hdist]
      nlinarith
    have hzT : (ρ : ℂ) • w + z₀ ∈ c.target := (hrO (ball_subset_ball hρr hzb)).1
    have hmem : (ρ : ℂ) • w + z₀ ∈ (c.restrOpen _ hs).target :=
      ⟨hzT, c.map_target hzT, by
        show c (c.symm ((ρ : ℂ) • w + z₀)) ∈ ball z₀ (3 * ρ)
        rw [c.right_inv hzT]
        exact hzb⟩
    show (pa_aff ((ρ : ℂ))⁻¹ ha z₀).symm w ∈ (c.restrOpen _ hs).target
    rw [hinv]
    exact hmem
  have htar2 : ∀ w ∈ ψ.target, (ρ : ℂ) • w + z₀ ∈ c.target ∧
      (ρ : ℂ) • w + z₀ ∈ ball z₀ (3 * ρ) := by
    intro w hw
    have hw' : (pa_aff ((ρ : ℂ))⁻¹ ha z₀).symm w ∈ (c.restrOpen _ hs).target := hw
    rw [hinv] at hw'
    obtain ⟨h1, -, h3⟩ := hw'
    refine ⟨h1, ?_⟩
    have h3' : c (c.symm ((ρ : ℂ) • w + z₀)) ∈ ball z₀ (3 * ρ) := h3
    rwa [c.right_inv h1] at h3'
  have hcl : closedBall (0 : Fin e → ℂ) 2 ⊆ ψ.target := fun w hw =>
    htar1 w (by
      have : ‖w‖ ≤ 2 := by simpa using hw
      linarith)

  have hbd : ∀ y ∈ ψ.target, (ψ.symm y ∈ bdry s ↔
      ∃ i ∈ S.filter (fun i => z₀ i = 0), y i = 0) := by
    intro w hw
    obtain ⟨hzT, hzb⟩ := htar2 w hw
    rw [hsymm, hb _ hzT]
    constructor
    · rintro ⟨i, hi, hzi⟩
      have hzi' : (ρ : ℂ) * w i + z₀ i = 0 := by simpa using hzi
      have h0 : z₀ i = 0 := by
        by_contra h0
        have h1 := hfar i h0
        have h2' : ‖z₀ i‖ ≤ ρ * ‖w‖ := by
          have h3 : z₀ i = -((ρ : ℂ) * w i) := eq_neg_of_add_eq_zero_right hzi'
          rw [h3, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ0.le]
          exact mul_le_mul_of_nonneg_left (norm_le_pi_norm w i) hρ0.le
        have h4 : ρ * ‖w‖ < 3 * ρ := by
          have := hzb
          rwa [Metric.mem_ball, dist_eq_norm, hdist] at this
        linarith
      refine ⟨i, Finset.mem_filter.2 ⟨hi, h0⟩, ?_⟩
      rw [h0, add_zero] at hzi'
      exact (mul_eq_zero.1 hzi').resolve_left hρC
    · rintro ⟨i, hi, hwi⟩
      obtain ⟨hiS, h0⟩ := Finset.mem_filter.1 hi
      exact ⟨i, hiS, by simp [hwi, h0]⟩
  obtain ⟨cc, hcc⟩ := rLoc_rescale_bound S m z₀ ρ hρ0 hρ8 hz₀1 hfar
  have hsmall : ∀ w : Fin e → ℂ, ‖w‖ ≤ 2 → ‖(ρ : ℂ) • w + z₀‖ < 3 / 2 := by
    intro w hw
    have h1 := norm_add_le ((ρ : ℂ) • w) z₀
    rw [hnorm] at h1
    nlinarith [norm_nonneg w]
  refine ⟨ψ, ⟨pa_compat_aff A _ (pa_compat_restr A _ (fun k => ⟨hAB.1 k j, hAB.2 j k⟩) _ hs) _ ha _,
    hcl, ⟨M + cc, S.filter (fun i => z₀ i = 0), m,
      fun i hi => hm i (Finset.mem_filter.1 hi).1, hbd, ?_⟩, ?_⟩, ?_, ?_, ?_⟩
  · intro w hw hnb
    have hw2 : ‖w‖ ≤ 2 := by simpa using hw
    have hz2 : (ρ : ℂ) • w + z₀ ∈ closedBall (0 : Fin e → ℂ) 2 := by
      have := hsmall w hw2
      simp only [mem_closedBall, dist_zero_right]
      linarith
    have hne : ∀ i ∈ S, z₀ i = 0 → w i ≠ 0 := fun i hi h0 hwi =>
      hnb ((hbd w (hcl hw)).2 ⟨i, Finset.mem_filter.2 ⟨hi, h0⟩, hwi⟩)
    rw [hsymm] at hnb ⊢
    have h1 := hr _ hz2 hnb
    have h3 := hcc w hw hne
    rw [abs_le] at h1 h3 ⊢
    constructor <;> linarith [h1.1, h1.2, h3.1, h3.2]
  · intro w hw hnb
    have hw32 : ‖w‖ < 3 / 2 := by simpa using hw
    have hz : (ρ : ℂ) • w + z₀ ∈ ball (0 : Fin e → ℂ) (3 / 2) := by
      simpa using hsmall w (by linarith)
    have hfun : ph ∘ ψ.symm = fun w => (ph ∘ c.symm) ((ρ : ℂ) • w + z₀) := by
      funext u
      simp [hsymm]
    rw [hfun]
    rw [hsymm] at hnb ⊢
    have h1 := fderiv_rescale_norm_le (ph ∘ c.symm) ρ hρ0 (by linarith) z₀ w
    have h3 : ‖fderiv ℝ (ph ∘ c.symm) ((ρ : ℂ) • w + z₀)‖ ≤ _ := hG j _ hz hnb
    refine (h1.trans h3).trans ?_
    set R := rW L s (c.symm ((ρ : ℂ) • w + z₀)) with hR
    have hR1 : 1 ≤ R := by
      have h4 : Real.exp 1 ≤ R := rW_ge L s hle _
      have h5 : (1 : ℝ) ≤ Real.exp 1 := by
        simpa using Real.add_one_le_exp (0 : ℝ) |>.trans (Real.exp_le_exp.2 zero_le_one)
      linarith
    have hR0 : 0 ≤ R := by linarith
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    exact mul_le_mul (le_abs_self _) (Real.rpow_le_rpow_of_exponent_le hR1 (le_abs_self _))
      (Real.rpow_nonneg hR0 _) (abs_nonneg _)
  · exact ⟨hx, hx, mem_ball_self (by positivity)⟩
  · have : ψ x = 0 := by
      show ((ρ : ℂ))⁻¹ • (c x - z₀) = 0
      simp [hz₀]
    rw [this]
    exact mem_ball_self one_pos
  · intro y hy
    have hy' : y ∈ (c.restrOpen _ hs).source := hy
    have h1 : y ∈ c.source := hy'.1
    have h3 : c y ∈ ball z₀ (3 * ρ) := hy'.2.2
    have h4 := (hrO (ball_subset_ball hρr h3)).2
    have h5 : c.symm (c y) ∈ th.U x := h4
    rwa [c.left_inv h1] at h5

theorem refine_adapted_atlas : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A B : FinHolAtlas e X) (L th : LocPot X) (s : X → X → ℂ) (ph : X → ℝ) (C₅ : ℝ), (∀ y, logNormSec L s y ≤ 0) → IsAdaptedAtlas A B L s → IsGradBound B L s ph C₅ → ∃ (B' : FinHolAtlas e X) (x : Fin B'.n → X), IsAdaptedAtlas A B' L s ∧ IsGradBound B' L s ph |C₅| ∧ ∀ j, (B'.chart j).source ⊆ th.U (x j) := by
  intro e X _ _ _ A B L th s ph C₅ hle hAd hG
  obtain ⟨hAB, h2, hcov, M, hM⟩ := hAd
  have hcov₀ := hcov
  choose jf hj hj1 using hcov₀
  have hgood := fun x : X => refine_local_chart A B L th s ph C₅ M hle hAB h2 hM hG (jf x) x (hj x) (hj1 x)
  choose φ hφg hφx hφ1 hφU using hgood
  have hU : ∀ x, φ x ⁻¹' ball 0 1 ∩ (φ x).source ∈ 𝓝 x := by
    intro x
    refine IsOpen.mem_nhds ?_ ⟨hφ1 x, hφx x⟩
    rw [Set.inter_comm]
    exact (φ x).continuousOn.isOpen_inter_preimage (φ x).open_source Metric.isOpen_ball
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover _ hU
  have hcov' : ∀ x, ∃ y ∈ t, x ∈ φ y ⁻¹' ball 0 1 ∩ (φ y).source := by
    intro x
    have : x ∈ (⊤ : Set X) := trivial
    rw [← ht] at this
    simp only [Set.mem_iUnion] at this
    obtain ⟨y, hy, hx⟩ := this
    exact ⟨y, hy, hx⟩
  obtain ⟨B', hAB', h1, h3⟩ := atlasOfCompat A (fun i => φ (t.equivFin.symm i))
    (fun i => (hφg _).1) (fun x => by
      obtain ⟨y, hy, hx⟩ := hcov' x
      exact ⟨t.equivFin ⟨y, hy⟩, by simpa using hx.2⟩)
  choose idx hidx using h3
  have hMx := fun x => (hφg x).2.2.1
  choose Mf hMf using hMx
  refine ⟨B', fun j => (t.equivFin.symm (idx j) : X), ⟨hAB', fun j => ?_, fun x => ?_,
    ∑ i, |Mf (t.equivFin.symm i : X)|, fun j => ?_⟩, fun j => ?_, fun j => ?_⟩
  · rw [hidx j]
    exact (hφg _).2.1
  · obtain ⟨y, hy, hx⟩ := hcov' x
    obtain ⟨j, hj⟩ := h1 (t.equivFin ⟨y, hy⟩)
    refine ⟨j, ?_, ?_⟩
    · rw [hj]
      simpa using hx.2
    · rw [hj]
      simpa using hx.1
  · obtain ⟨S, m, hm, hb, hr⟩ := hMf (t.equivFin.symm (idx j) : X)
    refine ⟨S, m, hm, ?_, ?_⟩
    · rw [hidx j]
      exact hb
    · rw [hidx j]
      intro y hy hnb
      refine (hr y hy hnb).trans ((le_abs_self _).trans ?_)
      exact Finset.single_le_sum (f := fun i => |Mf (t.equivFin.symm i : X)|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ (idx j))
  · rw [hidx j]
    exact (hφg _).2.2.2
  · rw [hidx j]
    exact hφU _

end

end GlobalTheory.CompanionTheory.Ar.Giv
