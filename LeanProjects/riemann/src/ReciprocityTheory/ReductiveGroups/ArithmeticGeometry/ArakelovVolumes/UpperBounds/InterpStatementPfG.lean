import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfF

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.HE

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric Filter Complex
open scoped ContDiff ComplexConjugate

noncomputable section

variable {n : ℕ} {U : Set (V n)}

theorem zeros_null (hU : IsOpen U) {g : V n → ℂ} (hg : DifferentiableOn ℂ g U)
    (hgn : ∀ W : Set (V n), IsOpen W → W ⊆ U → W.Nonempty → ∃ y ∈ W, g y ≠ 0) :
    volume {y | y ∈ U ∧ g y = 0} = 0 := by
  apply measure_null_of_locally_null
  intro x hx
  obtain ⟨ρ, hρ, hsub⟩ := Metric.isOpen_iff.1 hU x hx.1
  refine ⟨{y | y ∈ U ∧ g y = 0} ∩ ball x ρ, inter_mem_nhdsWithin _ (ball_mem_nhds x hρ), ?_⟩
  obtain ⟨y, hy, hgy⟩ := hgn (ball x ρ) isOpen_ball hsub ⟨x, mem_ball_self hρ⟩
  have := extNull n x ρ g (hg.mono hsub) ⟨y, hy, hgy⟩
  exact measure_mono_null (fun z (hz : z ∈ {y | y ∈ U ∧ g y = 0} ∩ ball x ρ) =>
    (⟨hz.2, hz.1.2⟩ : z ∈ ball x ρ ∩ {y | g y = 0})) this

def nsq (s : Fin n → V n → ℂ) (y : V n) : ℝ := ∑ k, Complex.normSq (s k y)

theorem nsq_nonneg (s : Fin n → V n → ℂ) (y : V n) : 0 ≤ nsq s y :=
  Finset.sum_nonneg fun k _ => Complex.normSq_nonneg _

theorem nsq_pos {s : Fin n → V n → ℂ} {y : V n} {k : Fin n} (h : s k y ≠ 0) : 0 < nsq s y := by
  unfold nsq
  exact lt_of_lt_of_le (Complex.normSq_pos.2 h)
    (Finset.single_le_sum (f := fun j => Complex.normSq (s j y)) (fun j _ => Complex.normSq_nonneg _)
      (Finset.mem_univ k))

theorem nsq_contDiffAt (hU : IsOpen U) {s : Fin n → V n → ℂ} (hs : ∀ k, DifferentiableOn ℂ (s k) U)
    {y : V n} (hy : y ∈ U) : ContDiffAt ℝ ∞ (nsq s) y := by
  unfold nsq
  exact ContDiffAt.sum fun k _ => normSq_contDiffAt (contDiffAt_of_punct hU (hs k) hy)

theorem nsq_continuousOn (hU : IsOpen U) {s : Fin n → V n → ℂ} (hs : ∀ k, DifferentiableOn ℂ (s k) U) :
    ContinuousOn (nsq s) U :=
  fun y hy => (nsq_contDiffAt hU hs hy).continuousAt.continuousWithinAt

def wgt (ψ : V n → ℝ) (s : Fin n → V n → ℂ) (y : V n) : ℝ := ψ y + n * Real.log (nsq s y)

theorem wgt_smooth (hU : IsOpen U) {ψ : V n → ℝ} (hψ : ContDiffOn ℝ ∞ ψ U) {s : Fin n → V n → ℂ}
    (hs : ∀ k, DifferentiableOn ℂ (s k) U) (k0 : Fin n) :
    ContDiffOn ℝ ∞ (wgt ψ s) {y | y ∈ U ∧ s k0 y ≠ 0} := by
  intro y hy
  obtain ⟨hyU, hy0⟩ := hy
  have hψy : ContDiffAt ℝ ∞ ψ y := hψ.contDiffAt (hU.mem_nhds hyU)
  have hpos : 0 < nsq s y := nsq_pos hy0
  have hl : ContDiffAt ℝ ∞ (fun w => Real.log (nsq s w)) y :=
    (Real.contDiffAt_log.2 hpos.ne').comp y (nsq_contDiffAt hU hs hyU)
  exact (hψy.add (contDiffAt_const.mul hl)).contDiffWithinAt

theorem wgt_levi (hU : IsOpen U) {ψ : V n → ℝ} (hψ : ContDiffOn ℝ ∞ ψ U) {s : Fin n → V n → ℂ}
    (hs : ∀ k, DifferentiableOn ℂ (s k) U) (k0 : Fin n) {y : V n} (hy : y ∈ U) (hy0 : s k0 y ≠ 0)
    (ξ : Fin n → ℂ) :
    (leviV n (fun w => (ψ w : ℂ)) y ξ).re ≤ (leviV n (fun w => (wgt ψ s w : ℂ)) y ξ).re := by
  have hU' := isOpen_punct hU (hs k0)
  have h1 : ContDiffAt ℝ 2 ψ y := (hψ.contDiffAt (hU.mem_nhds hy)).of_le two_le_inf
  have h2 : ContDiffAt ℝ 2 (fun w => Real.log (nsq s w)) y :=
    ((nsq_contDiffAt hU hs hy).log (nsq_pos hy0).ne').of_le two_le_inf
  have e1 : (fun w => (wgt ψ s w : ℂ)) = fun w => ((ψ w + (n : ℝ) * Real.log (nsq s w) : ℝ) : ℂ) := rfl
  rw [e1, Y.LocalMaximumSecondDerivative.leviV_ofReal_add h1 (contDiffAt_const.mul h2),
    Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul (n : ℝ) h2]
  have hlse : 0 ≤ (leviV n (fun w => (Real.log (nsq s w) : ℂ)) y ξ).re := lseV n n _ (fun k w => Complex.normSq (s k w)) hU'
    (fun k => Or.inr ⟨s k, ((contDiffOn_of_differentiableOn n (s k) U hU (hs k)).of_le two_le_inf).mono
      (fun w hw => hw.1), fun _ _ => rfl⟩)
    (fun w hw => nsq_pos hw.2) y ⟨hy, hy0⟩ ξ
  rw [Complex.add_re, Complex.re_ofReal_mul]
  nlinarith [mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) hlse]

def ann (ε : ℝ) : Set (V n) := {y | ε ≤ ‖y‖ ∧ ‖y‖ ≤ 2 * ε}

theorem ann_closed (ε : ℝ) : IsClosed (ann (n := n) ε) := by
  unfold ann
  first
  | exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  | (simp only [Set.setOf_and]
     exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const))

theorem ann_compact (ε : ℝ) : IsCompact (ann (n := n) ε) := by
  refine (isCompact_closedBall (0 : V n) (2 * ε)).of_isClosed_subset (ann_closed ε) ?_
  intro y hy
  have hy' : ε ≤ ‖y‖ ∧ ‖y‖ ≤ 2 * ε := hy
  rw [Metric.mem_closedBall, dist_zero_right]
  exact hy'.2

theorem cut_norm_le (ε : ℝ) (hε : 0 < ε) (y : V n) : ‖cut ε hε y‖ ≤ 1 := by
  unfold cut
  have h0 : 0 ≤ (bumpE ε hε : V n → ℝ) y := (bumpE ε hε).nonneg
  have h1 : (bumpE ε hε : V n → ℝ) y ≤ 1 := (bumpE ε hε).le_one
  first
  | (rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]; exact h1)
  | (rw [Complex.norm_of_nonneg h0]; exact h1)
  | simpa [abs_of_nonneg h0] using h1

theorem sq_le_two (a b : ℂ) : ‖b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖a - b‖ ^ 2 := by
  have h1 : ‖b‖ ≤ ‖a‖ + ‖a - b‖ := by
    calc ‖b‖ = ‖a - (a - b)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖a‖ + ‖a - b‖ := norm_sub_le _ _
  have h0 : 0 ≤ ‖b‖ := norm_nonneg _
  have h2 : ‖b‖ ^ 2 ≤ (‖a‖ + ‖a - b‖) ^ 2 := by
    have := mul_le_mul h1 h1 h0 (by positivity)
    nlinarith [this]
  nlinarith [h2, sq_nonneg (‖a‖ - ‖a - b‖)]

theorem interp_euclid (hU : IsOpen U) (e : V n → ℝ) (he : ContDiffOn ℝ ∞ e U)
    (hel : ∀ y ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun w => (e w : ℂ)) y ξ).re)
    (hec : ∀ a, IsCompact {y | y ∈ U ∧ e y ≤ a}) (he0 : ∀ y ∈ U, 0 ≤ e y)
    (s : Fin n → V n → ℂ) (hs : ∀ k, DifferentiableOn ℂ (s k) U) (k0 : Fin n)
    (hgn : ∀ W : Set (V n), IsOpen W → W ⊆ U → W.Nonempty → ∃ y ∈ W, s k0 y ≠ 0)
    (ψ : V n → ℝ) (hψ : ContDiffOn ℝ ∞ ψ U)
    (hψl : ∀ y ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun w => (ψ w : ℂ)) y ξ).re)
    (ε : ℝ) (hε : 0 < ε) (hball : closedBall (0 : V n) (2 * ε) ⊆ U)
    (hiso : ∀ y ∈ closedBall (0 : V n) (2 * ε), (∀ k, s k y = 0) → y = 0)
    (c : ℝ) (hc : 0 < c)
    (hpos : ∀ y ∈ closedBall (0 : V n) (2 * ε), ∀ ξ : Fin n → ℂ,
      c * ∑ j, ‖ξ j‖ ^ 2 ≤ (leviV n (fun w => (ψ w : ℂ)) y ξ).re) :
    ∃ F : V n → ℂ, DifferentiableOn ℂ F U ∧
      ∫⁻ y in U, ENNReal.ofReal (‖cut ε hε y - F y‖ ^ 2 * Real.exp (-ψ y) *
        nsq s y ^ (-(n : ℝ))) < ⊤ := by
  set U' := {y | y ∈ U ∧ s k0 y ≠ 0} with hU'def
  have hU' : IsOpen U' := isOpen_punct hU (hs k0)
  obtain ⟨M, hM0, hM⟩ := wdb_cut_bdd (n := n) ε hε
  have hannpos : ∀ y ∈ ann (n := n) ε, 0 < nsq s y := by
    intro y hy
    have hy0 : y ≠ 0 := by
      intro h0; have h1 := hy.1; rw [h0, norm_zero] at h1; linarith
    by_contra hle
    have h0 : nsq s y = 0 := le_antisymm (not_lt.1 hle) (nsq_nonneg s y)
    apply hy0
    refine hiso y (by simpa using hy.2) fun k => ?_
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => Complex.normSq_nonneg (s k y))).1 h0 k
      (Finset.mem_univ _)
    exact Complex.normSq_eq_zero.1 this
  have hannU : ann (n := n) ε ⊆ U := fun y hy => hball (by simpa using hy.2)
  have hexpc : ContinuousOn (fun y => Real.exp (-wgt ψ s y)) (ann (n := n) ε) := by
    refine Real.continuous_exp.comp_continuousOn (ContinuousOn.neg ?_)
    exact (hψ.continuousOn.mono hannU).add (continuousOn_const.mul
      (((nsq_continuousOn hU hs).mono hannU).log fun y hy => (hannpos y hy).ne'))
  obtain ⟨B, hB⟩ := (ann_compact (n := n) ε).exists_bound_of_continuousOn hexpc
  set h : V n → ENNReal := (ann (n := n) ε).indicator fun _ => ENNReal.ofReal (M / c) with hdef
  have hhm : Measurable h := measurable_const.indicator (ann_closed ε).measurableSet
  have hb : ∀ y ∈ U', ∀ ξ : Fin n → ℂ,
      ENNReal.ofReal (‖∑ j, wdb n j (cut ε hε) y * (starRingEnd ℂ) (ξ j)‖ ^ 2) ≤
        h y * ENNReal.ofReal (leviV n (fun w => (wgt ψ s w : ℂ)) y ξ).re := by
    intro y hy ξ
    by_cases hya : y ∈ ann (n := n) ε
    · have hl := wgt_levi hU hψ hs k0 hy.1 hy.2 ξ
      have hp := hpos y (by simpa using hya.2) ξ
      have hcs := norm_pair_sq_le (fun j => wdb n j (cut ε hε) y) ξ
      have hMy := hM y
      rw [hdef, Set.indicator_of_mem hya, ← ENNReal.ofReal_mul (div_nonneg hM0 hc.le)]
      apply ENNReal.ofReal_le_ofReal
      have hξ : 0 ≤ ∑ j, ‖ξ j‖ ^ 2 := Finset.sum_nonneg fun j _ => by positivity
      calc ‖∑ j, wdb n j (cut ε hε) y * (starRingEnd ℂ) (ξ j)‖ ^ 2
          ≤ (∑ j, ‖wdb n j (cut ε hε) y‖ ^ 2) * ∑ j, ‖ξ j‖ ^ 2 := hcs
        _ ≤ M * ∑ j, ‖ξ j‖ ^ 2 := mul_le_mul_of_nonneg_right hMy hξ
        _ = M / c * (c * ∑ j, ‖ξ j‖ ^ 2) := by field_simp
        _ ≤ M / c * (leviV n (fun w => (wgt ψ s w : ℂ)) y ξ).re :=
            mul_le_mul_of_nonneg_left (hp.trans hl) (div_nonneg hM0 hc.le)
    · have hz : ∀ j, wdb n j (cut ε hε) y = 0 := by
        intro j
        apply wdb_cut_zero
        simp only [ann, Set.mem_ofPred_eq, not_and_or, not_le] at hya
        exact hya
      simp [hz]
  obtain ⟨G, hGd, hest⟩ := hormander_open hU' (epunct e (s k0)) (epunct_smooth hU he (hs k0))
    (epunct_levi hU he hel (hs k0)) (epunct_compact hU he hec he0 (hs k0))
    (wgt ψ s) (wgt_smooth hU hψ hs k0)
    (fun y hy ξ => (hψl y hy.1 ξ).trans (wgt_levi hU hψ hs k0 hy.1 hy.2 ξ))
    (cut ε hε) (cut_contDiff ε hε).contDiffOn h hhm hb
  have hRHS : ∫⁻ y in U', h y * ENNReal.ofReal (Real.exp (-wgt ψ s y)) < ⊤ := by
    calc ∫⁻ y in U', h y * ENNReal.ofReal (Real.exp (-wgt ψ s y))
        ≤ ∫⁻ y, (ann (n := n) ε).indicator
            (fun _ => ENNReal.ofReal (M / c) * ENNReal.ofReal B) y := by
          refine (setLIntegral_le_lintegral _ _).trans (lintegral_mono fun y => ?_)
          by_cases hya : y ∈ ann (n := n) ε
          · rw [hdef, Set.indicator_of_mem hya, Set.indicator_of_mem hya]
            have := hB y hya
            rw [Real.norm_of_nonneg (Real.exp_pos _).le] at this
            exact mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal this) zero_le
          · rw [hdef, Set.indicator_of_notMem hya, Set.indicator_of_notMem hya, zero_mul]
      _ = ENNReal.ofReal (M / c) * ENNReal.ofReal B * volume (ann (n := n) ε) :=
          lintegral_indicator_const (ann_closed ε).measurableSet _
      _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
          (ann_compact ε).measure_lt_top
  have hL : ∀ p ∈ U, ∃ ρ > 0, ball p ρ ⊆ U ∧
      ∫⁻ y in ball p ρ \ {y | s k0 y = 0}, ENNReal.ofReal (‖G y‖ ^ 2) < ⊤ := by
    intro p hp
    obtain ⟨ρ', hρ', hsub'⟩ := Metric.isOpen_iff.1 hU p hp
    have hcb : closedBall p (ρ' / 2) ⊆ U := (closedBall_subset_ball (by linarith)).trans hsub'
    refine ⟨ρ' / 2, by positivity, ball_subset_closedBall.trans hcb, ?_⟩
    have hKc : ContinuousOn (fun y => Real.exp (ψ y) * nsq s y ^ n) (closedBall p (ρ' / 2)) :=
      ((Real.continuous_exp.comp_continuousOn hψ.continuousOn).mul
        ((nsq_continuousOn hU hs).pow n)).mono hcb
    obtain ⟨K, hK⟩ := (isCompact_closedBall p (ρ' / 2)).exists_bound_of_continuousOn hKc
    have hSm : MeasurableSet (ball p (ρ' / 2) \ {y | s k0 y = 0}) := by
      have := ((hs k0).continuousOn.mono (ball_subset_closedBall.trans hcb)).isOpen_inter_preimage
        isOpen_ball (isOpen_compl_singleton (x := (0 : ℂ)))
      exact this.measurableSet
    have hSU : ball p (ρ' / 2) \ {y | s k0 y = 0} ⊆ U' :=
      fun y hy => ⟨hcb (ball_subset_closedBall hy.1), hy.2⟩
    have hpt : ∀ y ∈ ball p (ρ' / 2) \ {y | s k0 y = 0}, ENNReal.ofReal (‖G y‖ ^ 2) ≤
        ENNReal.ofReal 2 + ENNReal.ofReal (2 * |K|) *
          ENNReal.ofReal (‖cut ε hε y - G y‖ ^ 2 * Real.exp (-wgt ψ s y)) := by
      intro y hy
      have hNp := nsq_pos (hSU hy).2
      have hKy := hK y (ball_subset_closedBall hy.1)
      have hew : Real.exp (wgt ψ s y) = Real.exp (ψ y) * nsq s y ^ n := by
        rw [wgt, Real.exp_add, ← Real.rpow_natCast, Real.rpow_def_of_pos hNp, mul_comm (Real.log _)]
      have hK' : Real.exp (wgt ψ s y) ≤ |K| := by
        rw [hew]; exact (le_abs_self _).trans (by rw [Real.norm_eq_abs] at hKy; exact hKy.trans (le_abs_self K))
      have hA := sq_le_two (cut ε hε y) (G y)
      have hc1 := cut_norm_le ε hε y
      set A := ‖cut ε hε y - G y‖ ^ 2
      have hAe : 0 ≤ A * Real.exp (-wgt ψ s y) := by positivity
      have hprod : A * Real.exp (-wgt ψ s y) * Real.exp (wgt ψ s y) = A := by
        rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
      have h2 : A ≤ |K| * (A * Real.exp (-wgt ψ s y)) := by
        have := mul_le_mul_of_nonneg_left hK' hAe
        rw [hprod] at this; linarith
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by norm_num) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hc2 : ‖cut ε hε y‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (cut ε hε y)]
      nlinarith
    calc ∫⁻ y in ball p (ρ' / 2) \ {y | s k0 y = 0}, ENNReal.ofReal (‖G y‖ ^ 2)
        ≤ ∫⁻ y in ball p (ρ' / 2) \ {y | s k0 y = 0}, (ENNReal.ofReal 2 + ENNReal.ofReal (2 * |K|) *
            ENNReal.ofReal (‖cut ε hε y - G y‖ ^ 2 * Real.exp (-wgt ψ s y))) :=
          setLIntegral_mono' hSm hpt
      _ = ENNReal.ofReal 2 * volume (ball p (ρ' / 2) \ {y | s k0 y = 0}) +
            ENNReal.ofReal (2 * |K|) * ∫⁻ y in ball p (ρ' / 2) \ {y | s k0 y = 0},
              ENNReal.ofReal (‖cut ε hε y - G y‖ ^ 2 * Real.exp (-wgt ψ s y)) := by
          rw [lintegral_add_left measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            setLIntegral_const]
      _ < ⊤ := by
          refine ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            ((measure_mono Set.diff_subset).trans_lt measure_ball_lt_top), ENNReal.mul_lt_top
            ENNReal.ofReal_lt_top ?_⟩
          exact ((lintegral_mono_set hSU).trans hest).trans_lt hRHS
  obtain ⟨F, hFd, hFeq⟩ := ext_glue hU (s k0) G (hs k0) hgn hGd hL
  refine ⟨F, hFd, ?_⟩
  have hnull := zeros_null hU (hs k0) hgn
  have hUsplit : U ⊆ U' ∪ {y | y ∈ U ∧ s k0 y = 0} := fun y hy => by
    by_cases h0 : s k0 y = 0
    · exact Or.inr ⟨hy, h0⟩
    · exact Or.inl ⟨hy, h0⟩
  calc ∫⁻ y in U, ENNReal.ofReal (‖cut ε hε y - F y‖ ^ 2 * Real.exp (-ψ y) * nsq s y ^ (-(n : ℝ)))
      ≤ ∫⁻ y in U' ∪ {y | y ∈ U ∧ s k0 y = 0},
          ENNReal.ofReal (‖cut ε hε y - F y‖ ^ 2 * Real.exp (-ψ y) * nsq s y ^ (-(n : ℝ))) :=
        lintegral_mono_set hUsplit
    _ ≤ (∫⁻ y in U', ENNReal.ofReal (‖cut ε hε y - F y‖ ^ 2 * Real.exp (-ψ y) *
            nsq s y ^ (-(n : ℝ)))) + ∫⁻ y in {y | y ∈ U ∧ s k0 y = 0},
            ENNReal.ofReal (‖cut ε hε y - F y‖ ^ 2 * Real.exp (-ψ y) * nsq s y ^ (-(n : ℝ))) :=
        lintegral_union_le _ _ _
    _ = ∫⁻ y in U', ENNReal.ofReal (‖cut ε hε y - G y‖ ^ 2 * Real.exp (-wgt ψ s y)) := by
        rw [setLIntegral_measure_zero _ _ hnull, add_zero]
        refine setLIntegral_congr_fun hU'.measurableSet (fun y hy => ?_)
        rw [hFeq hy, Real.rpow_def_of_pos (nsq_pos hy.2), mul_assoc, ← Real.exp_add]
        congr 3
        simp only [wgt]
        ring
    _ ≤ _ := hest
    _ < ⊤ := hRHS

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.HE
