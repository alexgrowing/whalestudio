import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LogIntCircle
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Set MvPolynomial

noncomputable section

namespace LogInt

variable {ι : Type*}

def indW (p : ι → Prop) [DecidablePred p] : ι → ℕ := fun x => if p x then 1 else 0

def scaleP (p : ι → Prop) [DecidablePred p] (a : ℂ) (u : ι → ℂ) : ι → ℂ :=
  fun x => if p x then a * u x else u x

def polydisc (ι : Type*) (r : ℝ) : Set (ι → ℂ) := Set.univ.pi fun _ => Metric.closedBall 0 r

theorem weight_indW (p : ι → Prop) [DecidablePred p] (m : ι →₀ ℕ) :
    Finsupp.weight (indW p) m = ∑ i ∈ m.support, if p i then m i else 0 := by
  rw [Finsupp.weight_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [indW]

theorem prod_scaleP (p : ι → Prop) [DecidablePred p] (a : ℂ) (u : ι → ℂ) (m : ι →₀ ℕ) :
    ∏ i ∈ m.support, scaleP p a u i ^ m i =
      a ^ Finsupp.weight (indW p) m * ∏ i ∈ m.support, u i ^ m i := by
  rw [weight_indW, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : p i <;> simp [scaleP, h, mul_pow]

theorem eval_scaleP (p : ι → Prop) [DecidablePred p] (a : ℂ) (u : ι → ℂ) (g : MvPolynomial ι ℂ)
    (D : ℕ) (hD : ∀ m ∈ g.support, Finsupp.weight (indW p) m ≤ D) :
    eval (scaleP p a u) g =
      ∑ d ∈ Finset.range (D + 1), eval u (weightedHomogeneousComponent (indW p) d g) * a ^ d := by
  classical
  have hc : ∀ d, eval u (weightedHomogeneousComponent (indW p) d g) =
      ∑ m ∈ g.support, (if Finsupp.weight (indW p) m = d then coeff m g else 0) *
        ∏ i ∈ m.support, u i ^ m i := by
    intro d
    rw [eval_eq]
    have hsub : (weightedHomogeneousComponent (indW p) d g).support ⊆ g.support := by
      intro m hm
      rw [mem_support_iff, coeff_weightedHomogeneousComponent] at hm
      rw [mem_support_iff]; intro h; exact hm (by simp [h])
    rw [Finset.sum_subset hsub (fun m _ hm => by rw [mem_support_iff, not_not] at hm; rw [hm, zero_mul])]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [coeff_weightedHomogeneousComponent]
  rw [eval_eq]
  simp_rw [hc, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [prod_scaleP]
  rw [Finset.sum_eq_single (Finsupp.weight (indW p) m)]
  · simp only [if_true]; ring
  · intro d _ hd; simp [Ne.symm hd]
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le (hD m hm))) h

theorem measurePreserving_mul_circleMap (θ : ℝ) :
    MeasurePreserving (fun z : ℂ => circleMap 0 1 θ * z) volume volume := by
  have h := (rotation (Circle.exp θ)).measurePreserving
  have e : (fun z : ℂ => circleMap 0 1 θ * z) = rotation (Circle.exp θ) := by
    funext z
    simp [rotation_apply, Circle.coe_exp, circleMap_zero]
  rw [e]
  exact h

theorem measurePreserving_scaleP [Fintype ι] (p : ι → Prop) [DecidablePred p] (θ : ℝ) :
    MeasurePreserving (scaleP p (circleMap 0 1 θ)) volume volume := by
  have := measurePreserving_pi (fun _ : ι => (volume : Measure ℂ)) (fun _ : ι => (volume : Measure ℂ))
    (f := fun x => if p x then (fun z : ℂ => circleMap 0 1 θ * z) else id)
    (fun x => by
      by_cases h : p x
      · simp only [h, if_true]; exact measurePreserving_mul_circleMap θ
      · simp only [h, if_false]; exact MeasurePreserving.id _)
  have e : scaleP p (circleMap 0 1 θ) =
      fun a x => (if p x then (fun z : ℂ => circleMap 0 1 θ * z) else id) (a x) := by
    funext u x
    by_cases h : p x <;> simp [scaleP, h]
  rw [e]
  exact this

theorem measurable_scaleP [Fintype ι] (p : ι → Prop) [DecidablePred p] :
    Measurable (Function.uncurry fun θ : ℝ => scaleP p (circleMap 0 1 θ) : ℝ × (ι → ℂ) → ι → ℂ) := by
  apply Continuous.measurable
  refine continuous_pi fun x => ?_
  by_cases h : p x
  · simp only [Function.uncurry, scaleP, h, if_true]
    exact ((continuous_circleMap 0 1).comp continuous_fst).mul ((continuous_apply x).comp continuous_snd)
  · simp only [Function.uncurry, scaleP, h, if_false]
    exact (continuous_apply x).comp continuous_snd

theorem norm_scaleP_circleMap (p : ι → Prop) [DecidablePred p] (θ : ℝ) (u : ι → ℂ) (x : ι) :
    ‖scaleP p (circleMap 0 1 θ) u x‖ = ‖u x‖ := by
  by_cases h : p x <;> simp [scaleP, h]

theorem scale_preimage_polydisc (p : ι → Prop) [DecidablePred p] (θ : ℝ) (r : ℝ) :
    scaleP p (circleMap 0 1 θ) ⁻¹' polydisc ι r = polydisc ι r := by
  ext u
  simp [polydisc, norm_scaleP_circleMap]

theorem measurableSet_polydisc [Fintype ι] (r : ℝ) : MeasurableSet (polydisc ι r) :=
  MeasurableSet.univ_pi fun _ => Metric.isClosed_closedBall.measurableSet

theorem isCompact_polydisc (r : ℝ) : IsCompact (polydisc ι r) :=
  isCompact_univ_pi fun _ => isCompact_closedBall 0 r

theorem volume_polydisc_ne_top [Fintype ι] (r : ℝ) : volume (polydisc ι r) ≠ ⊤ :=
  (isCompact_polydisc r).measure_lt_top.ne

theorem integrableOn_log_norm_closedBall (r : ℝ) :
    IntegrableOn (fun z : ℂ => Real.log ‖z‖) (Metric.closedBall 0 r) := by
  rw [← integrable_indicator_iff Metric.isClosed_closedBall.measurableSet]
  have e : (Metric.closedBall (0 : ℂ) r).indicator (fun z : ℂ => Real.log ‖z‖) =
      fun z => (Iic r).indicator Real.log ‖z‖ := by
    funext z
    simp [Set.indicator, Metric.mem_closedBall, dist_zero_right]
  rw [e, integrable_fun_norm_addHaar volume, Complex.finrank_real_complex]
  have e2 : (fun y : ℝ => y ^ (2 - 1) • (Iic r).indicator Real.log y) =
      (Iic r).indicator (fun y => y * Real.log y) := by
    funext y
    by_cases h : y ∈ Iic r <;> simp [Set.indicator, h]
  rw [e2, IntegrableOn, integrable_indicator_iff measurableSet_Iic, IntegrableOn,
    Measure.restrict_restrict measurableSet_Iic]
  exact (Real.continuous_mul_log.integrableOn_Icc (a := 0) (b := r)).mono_set
    (fun y hy => ⟨le_of_lt hy.2, hy.1⟩)

theorem integrableOn_log_norm_coord [Fintype ι] (r : ℝ) (x : ι) :
    IntegrableOn (fun u : ι → ℂ => Real.log ‖u x‖) (polydisc ι r) := by
  have : IsFiniteMeasure ((volume : Measure ℂ).restrict (Metric.closedBall 0 r)) :=
    isFiniteMeasure_restrict.mpr (measure_closedBall_lt_top).ne
  rw [IntegrableOn, polydisc, volume_pi, Measure.restrict_pi_pi]
  exact integrable_comp_eval (μ := fun _ : ι => (volume : Measure ℂ).restrict (Metric.closedBall 0 r))
    (i := x) (integrableOn_log_norm_closedBall r)

theorem abs_log_eval_monomial_le (m : ι →₀ ℕ) (c : ℂ) (u : ι → ℂ) :
    |Real.log ‖eval u (monomial m c)‖| ≤
      |Real.log ‖c‖| + ∑ i ∈ m.support, (m i : ℝ) * |Real.log ‖u i‖| := by
  have hnn : 0 ≤ |Real.log ‖c‖| + ∑ i ∈ m.support, (m i : ℝ) * |Real.log ‖u i‖| := by positivity
  rw [eval_monomial, Finsupp.prod]
  by_cases h : ∀ i ∈ m.support, u i ≠ 0
  · by_cases hc : c = 0
    · simpa [hc] using hnn
    · have hp : ∏ i ∈ m.support, u i ^ m i ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero _ (h i hi)
      rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hc) (norm_ne_zero_iff.mpr hp), norm_prod,
        Real.log_prod (fun i hi => norm_ne_zero_iff.mpr (pow_ne_zero _ (h i hi)))]
      simp_rw [norm_pow, Real.log_pow]
      refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [abs_mul, Nat.abs_cast]
  · push Not at h
    obtain ⟨i, hi, hu⟩ := h
    have : ∏ i ∈ m.support, u i ^ m i = 0 :=
      Finset.prod_eq_zero hi (by rw [hu]; exact zero_pow (Finsupp.mem_support_iff.mp hi))
    simpa [this] using hnn

theorem weight_indW_eq (x : ι) [DecidableEq ι] (m : ι →₀ ℕ) :
    Finsupp.weight (indW (· = x)) m = m x := by
  rw [weight_indW, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · exact (Finsupp.notMem_support_iff.mp h).symm

theorem weight_indW_le (p : ι → Prop) [DecidablePred p] (m : ι →₀ ℕ) :
    Finsupp.weight (indW p) m ≤ m.sum fun _ e => e := by
  rw [weight_indW, Finsupp.sum]
  exact Finset.sum_le_sum fun i _ => by split_ifs <;> simp

theorem eq_monomial_of_homog [DecidableEq ι] (g : MvPolynomial ι ℂ) (hg : g ≠ 0)
    (h : ∀ x, ∃ d, IsWeightedHomogeneous (indW (· = x)) g d) :
    ∃ m, g = monomial m (coeff m g) ∧ coeff m g ≠ 0 := by
  choose d hd using h
  have key : ∀ m ∈ g.support, ∀ x, m x = d x := by
    intro m hm x
    have := hd x (mem_support_iff.mp hm)
    rwa [weight_indW_eq] at this
  obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.mpr hg
  refine ⟨m, ?_, mem_support_iff.mp hm⟩
  ext n
  rw [coeff_monomial]
  split_ifs with hmn
  · rw [hmn]
  · by_contra hne
    have hn : n ∈ g.support := mem_support_iff.mpr hne
    exact hmn (Finsupp.ext fun x => (key m hm x).trans (key n hn x).symm)

def nonHomog [Fintype ι] [DecidableEq ι] (g : MvPolynomial ι ℂ) : Finset ι :=
  by classical exact Finset.univ.filter fun x => ¬ ∃ d, IsWeightedHomogeneous (indW (· = x)) g d

theorem isWeightedHomogeneous_component_of (w w' : ι → ℕ) (g : MvPolynomial ι ℂ) (d e : ℕ)
    (h : IsWeightedHomogeneous w g e) :
    IsWeightedHomogeneous w (weightedHomogeneousComponent w' d g) e := by
  intro m hm
  rw [coeff_weightedHomogeneousComponent] at hm
  split_ifs at hm
  · exact h hm
  · exact absurd rfl hm

theorem logPoly [Fintype ι] [DecidableEq ι] (r : ℝ) :
    ∀ (N : ℕ) (g : MvPolynomial ι ℂ), (nonHomog g).card = N → g ≠ 0 →
      IntegrableOn (fun u => Real.log ‖eval u g‖) (polydisc ι r) ∧
        ∀ᵐ u ∂(volume.restrict (polydisc ι r)), eval u g ≠ 0 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro g hN hg
  by_cases h0 : ∀ x, ∃ d, IsWeightedHomogeneous (indW (· = x)) g d
  ·
    obtain ⟨m, hgm, hc⟩ := eq_monomial_of_homog g hg h0
    rw [hgm]
    have hmeas : Measurable fun u : ι → ℂ => Real.log ‖eval u (monomial m (coeff m g))‖ :=
      Real.measurable_log.comp (continuous_eval _).measurable.norm
    refine ⟨?_, ?_⟩
    · refine Integrable.mono' (g := fun u => |Real.log ‖coeff m g‖| +
          ∑ i ∈ m.support, (m i : ℝ) * |Real.log ‖u i‖|) ?_ hmeas.aestronglyMeasurable
          (Filter.Eventually.of_forall fun u => ?_)
      · have : IsFiniteMeasure (volume.restrict (polydisc ι r)) :=
          isFiniteMeasure_restrict.mpr (volume_polydisc_ne_top r)
        exact (integrable_const _).add (integrable_finsetSum _ fun i _ =>
          ((integrableOn_log_norm_coord r i).abs.const_mul _))
      · rw [Real.norm_eq_abs]
        exact abs_log_eval_monomial_le m _ u
    · have hnull : volume (⋃ i ∈ m.support, {u : ι → ℂ | u i = 0}) = 0 := by
        refine (measure_biUnion_null_iff (Finset.countable_toSet _)).mpr fun i _ => ?_
        rw [volume_pi]
        exact Measure.pi_hyperplane _ i 0
      have hae : ∀ᵐ u ∂(volume : Measure (ι → ℂ)), u ∉ ⋃ i ∈ m.support, {u : ι → ℂ | u i = 0} :=
        measure_eq_zero_iff_ae_notMem.mp hnull
      refine ae_restrict_of_ae ?_
      filter_upwards [hae] with u hu
      simp only [mem_iUnion, mem_ofPred_eq, not_exists] at hu
      rw [eval_monomial, Finsupp.prod]
      exact mul_ne_zero hc (Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero _ (hu i hi))
  · push Not at h0
    obtain ⟨x, hx⟩ := h0
    have hxN : x ∈ nonHomog g := by
      simp only [nonHomog, Finset.mem_filter, Finset.mem_univ, true_and, not_exists]
      exact hx
    obtain ⟨m0, hm0⟩ := MvPolynomial.support_nonempty.mpr hg
    set w := indW (· = x) with hw
    set d0 := Finsupp.weight w m0 with hd0
    set g' := weightedHomogeneousComponent w d0 g with hg'
    have hg'0 : g' ≠ 0 := by
      intro h
      have := congrArg (coeff m0) h
      rw [hg', coeff_weightedHomogeneousComponent, if_pos rfl, coeff_zero] at this
      exact mem_support_iff.mp hm0 this
    have hsub : nonHomog g' ⊆ (nonHomog g).erase x := by
      intro y hy
      simp only [nonHomog, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hy ⊢
      refine ⟨?_, ?_⟩
      · rintro rfl
        exact hy ⟨d0, weightedHomogeneousComponent_isWeightedHomogeneous _ _⟩
      · rintro ⟨e, he⟩
        exact hy ⟨e, isWeightedHomogeneous_component_of _ _ g d0 e he⟩
    have hlt : (nonHomog g').card < N := by
      rw [← hN]
      exact (Finset.card_le_card hsub).trans_lt (Finset.card_erase_lt_of_mem hxN)
    obtain ⟨ih1, ih2⟩ := ih _ hlt g' rfl hg'0
    obtain ⟨M, hM⟩ := (isCompact_polydisc (ι := ι) r).exists_bound_of_continuousOn
      (continuous_eval g).continuousOn
    have hD : ∀ m ∈ g.support, Finsupp.weight w m ≤ g.totalDegree :=
      fun m hm => (weight_indW_le _ m).trans (le_totalDegree hm)
    exact circle_lemma volume (polydisc ι r) (measurableSet_polydisc r) (volume_polydisc_ne_top r)
      (fun θ => scaleP (· = x) (circleMap 0 1 θ)) (measurable_scaleP _)
      (fun θ => measurePreserving_scaleP _ θ) (fun θ => scale_preimage_polydisc _ θ r)
      (fun u => eval u g) (continuous_eval g).measurable
      (fun d u => eval u (weightedHomogeneousComponent w d g)) g.totalDegree d0
      (hD m0 hm0) (fun θ u => eval_scaleP _ _ u g _ hD) ih1 ih2 M hM

theorem integrableOn_log_norm_eval [Fintype ι] (g : MvPolynomial ι ℂ) (hg : g ≠ 0) (r : ℝ) :
    IntegrableOn (fun u => Real.log ‖eval u g‖) (polydisc ι r) := by
  classical
  exact (logPoly r _ g rfl hg).1

theorem ae_eval_ne_zero [Fintype ι] (g : MvPolynomial ι ℂ) (hg : g ≠ 0) (r : ℝ) :
    ∀ᵐ u ∂(volume.restrict (polydisc ι r)), eval u g ≠ 0 := by
  classical
  exact (logPoly r _ g rfl hg).2

end LogInt

end

end GroundTheory.Heights₂.Heights
