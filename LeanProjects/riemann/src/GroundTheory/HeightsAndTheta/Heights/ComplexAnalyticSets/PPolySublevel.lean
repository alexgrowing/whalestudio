import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.IsAddHaarMeasureHausdorffMeasureEuclideanSpaceCo
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory MvPolynomial

open scoped ENNReal

noncomputable section

theorem pow_card_le_norm_eval_prod_X_sub_C (z : ℂ) {c : ℝ} (hc : 0 ≤ c) :
    ∀ s : Multiset ℂ, (∀ r ∈ s, c ≤ ‖z - r‖) →
      c ^ Multiset.card s ≤ ‖(s.map fun r => Polynomial.X - Polynomial.C r).prod.eval z‖ := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | cons r s ih =>
    intro h
    rw [Multiset.map_cons, Multiset.prod_cons, Polynomial.eval_mul, norm_mul, Multiset.card_cons,
      pow_succ, mul_comm]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact mul_le_mul (h r (Multiset.mem_cons_self r s))
      (ih fun r' hr' => h r' (Multiset.mem_cons_of_mem hr')) (pow_nonneg hc _) (norm_nonneg _)

theorem volume_sublevel_one_var (p : Polynomial ℂ) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (ha : η < ‖p.leadingCoeff‖ ^ 2) :
    volume {z : ℂ | ‖p.eval z‖ ≤ η} ≤
      ENNReal.ofReal (4 * Real.pi * p.natDegree * η ^ ((p.natDegree : ℝ)⁻¹)) := by
  classical
  have ha0 : 0 < ‖p.leadingCoeff‖ := by
    rcases (norm_nonneg p.leadingCoeff).eq_or_lt with h | h
    · rw [← h] at ha; nlinarith
    · exact h
  rcases Nat.eq_zero_or_pos p.natDegree with h0 | hpos
  · have hc : ∀ z, p.eval z = p.leadingCoeff := by
      intro z
      have h1 : p.leadingCoeff = p.coeff 0 := by rw [Polynomial.leadingCoeff, h0]
      rw [h1]
      conv_lhs => rw [Polynomial.eq_C_of_natDegree_eq_zero h0]
      rw [Polynomial.eval_C]
    have hgt : η < ‖p.leadingCoeff‖ := by
      by_contra hle
      push Not at hle
      nlinarith
    have hempty : {z : ℂ | ‖p.eval z‖ ≤ η} = ∅ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le, hc]
      exact hgt
    rw [hempty, measure_empty]
    exact bot_le
  set m := p.natDegree with hm
  set a := p.leadingCoeff with ha_def
  have hm0 : m ≠ 0 := hpos.ne'
  set ρ : ℝ := (η / ‖a‖) ^ ((m : ℝ)⁻¹) with hρ_def
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos (div_pos hη ha0) _
  have hρm : ρ ^ m = η / ‖a‖ := Real.rpow_inv_natCast_pow (div_pos hη ha0).le hm0
  have hroots : Multiset.card p.roots = m := IsAlgClosed.card_roots_eq_natDegree
  have hsub : {z : ℂ | ‖p.eval z‖ ≤ η} ⊆
      ⋃ r ∈ p.roots.toFinset, Metric.closedBall r (2 * ρ) := by
    intro z hz
    by_contra hcon
    simp only [Set.mem_iUnion, Metric.mem_closedBall, Multiset.mem_toFinset, not_exists,
      not_le] at hcon
    have hfac := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hroots
    have hlow := pow_card_le_norm_eval_prod_X_sub_C z (by positivity : (0 : ℝ) ≤ 2 * ρ) p.roots
      (fun r hr => by rw [← dist_eq_norm]; exact (hcon r hr).le)
    have heval : ‖p.eval z‖ =
        ‖a‖ * ‖(p.roots.map fun r => Polynomial.X - Polynomial.C r).prod.eval z‖ := by
      conv_lhs => rw [← hfac]
      rw [Polynomial.eval_mul, Polynomial.eval_C, norm_mul]
    rw [hroots, mul_pow] at hlow
    have hz' : ‖p.eval z‖ ≤ ‖a‖ * ρ ^ m := by
      rw [hρm, mul_div_cancel₀ _ ha0.ne']; exact hz
    have h2 : (1 : ℝ) < 2 ^ m := one_lt_pow₀ one_lt_two hm0
    have hρpos : 0 < ρ ^ m := pow_pos hρ0 m
    have h3 : ‖a‖ * (2 ^ m * ρ ^ m) ≤ ‖a‖ * ‖(p.roots.map fun r => Polynomial.X -
        Polynomial.C r).prod.eval z‖ := mul_le_mul_of_nonneg_left hlow ha0.le
    have h4 : ‖a‖ * ρ ^ m < ‖a‖ * (2 ^ m * ρ ^ m) := mul_lt_mul_of_pos_left (by nlinarith) ha0
    linarith
  have hρsq : ρ ^ 2 ≤ η ^ ((m : ℝ)⁻¹) := by
    have hη' : 0 ≤ η ^ ((m : ℝ)⁻¹) := Real.rpow_nonneg hη.le _
    rw [← pow_le_pow_iff_left₀ (by positivity) hη' hm0, ← pow_mul, mul_comm, pow_mul, hρm,
      Real.rpow_inv_natCast_pow hη.le hm0, div_pow, div_le_iff₀ (by positivity)]
    nlinarith
  have hcard : (p.roots.toFinset.card : ℝ) ≤ m := by
    exact_mod_cast hroots ▸ Multiset.toFinset_card_le p.roots
  calc volume {z : ℂ | ‖p.eval z‖ ≤ η}
      ≤ volume (⋃ r ∈ p.roots.toFinset, Metric.closedBall r (2 * ρ)) := measure_mono hsub
    _ ≤ ∑ r ∈ p.roots.toFinset, volume (Metric.closedBall r (2 * ρ)) :=
        measure_biUnion_finset_le _ _
    _ ≤ ENNReal.ofReal (4 * Real.pi * m * η ^ ((m : ℝ)⁻¹)) := by
        simp only [Complex.volume_closedBall, Finset.sum_const, nsmul_eq_mul]
        rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have := Real.pi_pos
        calc (p.roots.toFinset.card : ℝ) * ((2 * ρ) ^ 2 * Real.pi)
            = (p.roots.toFinset.card : ℝ) * (4 * Real.pi * ρ ^ 2) := by ring
          _ ≤ m * (4 * Real.pi * η ^ ((m : ℝ)⁻¹)) := by gcongr
          _ = 4 * Real.pi * m * η ^ ((m : ℝ)⁻¹) := by ring

theorem polySublevel_zero (Q : MvPolynomial (Fin 0) ℂ) (hQ : Q ≠ 0) (R : ℝ) :
    ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ ∀ η : ℝ, 0 < η → η ≤ 1 →
      volume {x : Fin 0 → ℂ | x ∈ Metric.ball 0 R ∧ ‖eval x Q‖ ≤ η} ≤ ENNReal.ofReal (C * η ^ α) := by
  have hQc := eq_C_of_isEmpty Q
  have hc : Q.coeff 0 ≠ 0 := fun h => hQ (by rw [hQc, h, map_zero])
  have hc0 : 0 < ‖Q.coeff 0‖ := norm_pos_iff.2 hc
  refine ⟨‖Q.coeff 0‖⁻¹, 1, inv_pos.2 hc0, one_pos, fun η hη hη1 => ?_⟩
  by_cases hle : ‖Q.coeff 0‖ ≤ η
  · calc volume {x : Fin 0 → ℂ | x ∈ Metric.ball 0 R ∧ ‖eval x Q‖ ≤ η}
        ≤ volume (Set.univ : Set (Fin 0 → ℂ)) := measure_mono (Set.subset_univ _)
      _ = 1 := by simp [volume_pi]
      _ ≤ ENNReal.ofReal (‖Q.coeff 0‖⁻¹ * η ^ (1 : ℝ)) := by
        rw [Real.rpow_one, ← ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        rw [le_inv_mul_iff₀ hc0, mul_one]
        exact hle
  · have hempty : {x : Fin 0 → ℂ | x ∈ Metric.ball 0 R ∧ ‖eval x Q‖ ≤ η} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_le]
      intro _
      rw [hQc, eval_C]
      exact lt_of_not_ge hle
    rw [hempty, measure_empty]
    exact bot_le

theorem PolySublevel.proof : PolySublevel.Statement := by
  intro d
  induction d with
  | zero => intro Q hQ R _; exact polySublevel_zero Q hQ R
  | succ d ih =>
    intro Q hQ R hR
    set P := finSuccEquiv ℂ d Q with hP_def
    set m := P.natDegree with hm
    set q := P.leadingCoeff with hq_def
    have hP : P ≠ 0 := by
      intro h; apply hQ; rw [← (finSuccEquiv ℂ d).symm_apply_apply Q, ← hP_def, h, map_zero]
    have hq : q ≠ 0 := Polynomial.leadingCoeff_ne_zero.2 hP
    obtain ⟨C', α', hC', hα', hIH⟩ := ih q hq R hR
    set W : ℝ := (volume (Metric.ball (0 : ℂ) R)).toReal with hW
    set V : ℝ := (volume (Metric.ball (0 : Fin d → ℂ) R)).toReal with hV
    have hW0 : 0 ≤ W := ENNReal.toReal_nonneg
    have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
    refine ⟨W * C' + 4 * Real.pi * m * V + 1, min (α' / 2) ((m : ℝ) + 1)⁻¹,
      by positivity, lt_min (by positivity) (by positivity), fun η hη hη1 => ?_⟩
    set S := {x : Fin (d + 1) → ℂ | x ∈ Metric.ball 0 R ∧ ‖eval x Q‖ ≤ η} with hS_def
    have hS : MeasurableSet S := Metric.isOpen_ball.measurableSet.inter
      (isClosed_le (MvPolynomial.continuous_eval Q).norm continuous_const).measurableSet
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℂ) 0
    have he := measurePreserving_piFinSuccAbove (fun _ : Fin (d + 1) => (volume : Measure ℂ)) 0
    have hmem : ∀ z y, (z, y) ∈ e.symm ⁻¹' S ↔
        (‖z‖ < R ∧ y ∈ Metric.ball 0 R) ∧ ‖(Polynomial.map (eval y) P).eval z‖ ≤ η := by
      intro z y
      simp only [Set.mem_preimage, e, MeasurableEquiv.piFinSuccAbove_symm_apply, hS_def,
        Set.mem_ofPred_eq, mem_ball_zero_iff, pi_norm_lt_iff hR, Fin.forall_fin_succ]
      simp [← eval_eq_eval_mv_eval', hP_def]
      intro _ _
      rfl
    have hvol : volume S = (volume.prod (Measure.pi fun _ : Fin d => (volume : Measure ℂ)))
        (e.symm ⁻¹' S) := ((MeasurePreserving.symm e he).measure_preimage hS.nullMeasurableSet).symm
    set A := {y : Fin d → ℂ | y ∈ Metric.ball 0 R ∧ ‖eval y q‖ ≤ Real.sqrt η} with hA_def
    have hA : MeasurableSet A := Metric.isOpen_ball.measurableSet.inter
      (isClosed_le (MvPolynomial.continuous_eval q).norm continuous_const).measurableSet
    have hfib : ∀ y : Fin d → ℂ, volume ((fun z => (z, y)) ⁻¹' (e.symm ⁻¹' S)) ≤
        A.indicator (fun _ => volume (Metric.ball (0 : ℂ) R)) y +
          (Metric.ball (0 : Fin d → ℂ) R).indicator
            (fun _ => ENNReal.ofReal (4 * Real.pi * m * η ^ ((m : ℝ)⁻¹))) y := by
      intro y
      by_cases hy : y ∈ Metric.ball (0 : Fin d → ℂ) R
      · by_cases hyA : ‖eval y q‖ ≤ Real.sqrt η
        · rw [Set.indicator_of_mem (show y ∈ A from ⟨hy, hyA⟩)]
          refine le_trans (measure_mono fun z hz => ?_) le_self_add
          rw [Set.mem_preimage, hmem] at hz
          exact mem_ball_zero_iff.2 hz.1.1
        · rw [Set.indicator_of_mem hy]
          refine le_trans ?_ le_add_self
          have hlc : eval y q ≠ 0 := by
            intro h; rw [h, norm_zero] at hyA; exact hyA (Real.sqrt_nonneg η)
          have hdeg : (Polynomial.map (eval y) P).natDegree = m :=
            Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hlc
          have hlead : (Polynomial.map (eval y) P).leadingCoeff = eval y q :=
            Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hlc
          have hsq : η < ‖(Polynomial.map (eval y) P).leadingCoeff‖ ^ 2 := by
            rw [hlead]
            push Not at hyA
            exact (Real.sqrt_lt' (lt_of_le_of_lt (Real.sqrt_nonneg η) hyA)).1 hyA
          have h1 := volume_sublevel_one_var (Polynomial.map (eval y) P) hη hη1 hsq
          rw [hdeg] at h1
          refine le_trans (measure_mono fun z hz => ?_) h1
          rw [Set.mem_preimage, hmem] at hz
          exact hz.2
      · have h0 : (fun z => (z, y)) ⁻¹' (e.symm ⁻¹' S) = ∅ := by
          ext z
          simp only [Set.mem_preimage, hmem, Set.mem_empty_iff_false, iff_false]
          exact fun h => hy h.1.2
        rw [h0, measure_empty]
        exact bot_le
    have hint : volume S ≤ volume (Metric.ball (0 : ℂ) R) * volume A +
        ENNReal.ofReal (4 * Real.pi * m * η ^ ((m : ℝ)⁻¹)) *
          volume (Metric.ball (0 : Fin d → ℂ) R) := by
      rw [hvol, Measure.prod_apply_symm (e.symm.measurable hS)]
      refine le_trans (lintegral_mono hfib) (le_of_eq ?_)
      rw [lintegral_add_left (measurable_const.indicator hA), lintegral_indicator_const hA,
        lintegral_indicator_const Metric.isOpen_ball.measurableSet]
      rfl
    have hA_le : volume A ≤ ENNReal.ofReal (C' * Real.sqrt η ^ α') :=
      hIH (Real.sqrt η) (Real.sqrt_pos.2 hη) ((Real.sqrt_le_sqrt hη1).trans_eq Real.sqrt_one)
    have hc1 : volume (Metric.ball (0 : ℂ) R) = ENNReal.ofReal W :=
      (ENNReal.ofReal_toReal measure_ball_lt_top.ne).symm
    have hc2 : volume (Metric.ball (0 : Fin d → ℂ) R) = ENNReal.ofReal V :=
      (ENNReal.ofReal_toReal measure_ball_lt_top.ne).symm
    have hsqrt : Real.sqrt η ^ α' ≤ η ^ min (α' / 2) ((m : ℝ) + 1)⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hη.le]
      apply Real.rpow_le_rpow_of_exponent_ge hη hη1
      linarith [min_le_left (α' / 2) ((m : ℝ) + 1)⁻¹]
    have hmη : (m : ℝ) * η ^ ((m : ℝ)⁻¹) ≤ m * η ^ min (α' / 2) ((m : ℝ) + 1)⁻¹ := by
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · simp [h0]
      · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg m)
        apply Real.rpow_le_rpow_of_exponent_ge hη hη1
        calc min (α' / 2) ((m : ℝ) + 1)⁻¹ ≤ ((m : ℝ) + 1)⁻¹ := min_le_right _ _
          _ ≤ (m : ℝ)⁻¹ := inv_anti₀ (Nat.cast_pos.2 hpos) (by linarith)
    have hreal : W * (C' * Real.sqrt η ^ α') + 4 * Real.pi * m * η ^ ((m : ℝ)⁻¹) * V ≤
        (W * C' + 4 * Real.pi * m * V + 1) * η ^ min (α' / 2) ((m : ℝ) + 1)⁻¹ := by
      have hpα : 0 ≤ η ^ min (α' / 2) ((m : ℝ) + 1)⁻¹ := Real.rpow_nonneg hη.le _
      have hpi := Real.pi_pos
      nlinarith [mul_le_mul_of_nonneg_left hsqrt (mul_nonneg hW0 hC'.le),
        mul_le_mul_of_nonneg_left hmη (mul_nonneg (by positivity : (0 : ℝ) ≤ 4 * Real.pi) hV0)]
    calc volume S ≤ volume (Metric.ball (0 : ℂ) R) * volume A +
          ENNReal.ofReal (4 * Real.pi * m * η ^ ((m : ℝ)⁻¹)) *
            volume (Metric.ball (0 : Fin d → ℂ) R) := hint
      _ ≤ ENNReal.ofReal W * ENNReal.ofReal (C' * Real.sqrt η ^ α') +
          ENNReal.ofReal (4 * Real.pi * m * η ^ ((m : ℝ)⁻¹)) * ENNReal.ofReal V := by
        rw [hc1, hc2]
        exact add_le_add (by gcongr) le_rfl
      _ = ENNReal.ofReal (W * (C' * Real.sqrt η ^ α') +
          4 * Real.pi * m * η ^ ((m : ℝ)⁻¹) * V) := by
        rw [← ENNReal.ofReal_mul hW0, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
      _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

end

end GroundTheory.Heights₂.Heights

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

theorem PolySublevel.proof : PolySublevel.Statement :=
  PolySublevel.equiv.1 GroundTheory.Heights₂.Heights.PolySublevel.proof

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
