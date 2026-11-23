import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SiegelMeanCc
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaussianQuadricDensityExistsPosContinuous

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean

noncomputable section

namespace GlobalTheory.GaussMean.Trunc

open GlobalTheory.GaussMean.Density

def prodFun (g : ℝ → ℝ) {n : ℕ} (y : Fin n → ℂ) : ℝ := ∏ i, g (‖y i‖ ^ 2)

def dens (g : ℝ → ℝ) {n : ℕ} (ε : Fin (n + 1) → Bool) (t : ℝ) : ℝ :=
  Real.pi * ∫ y : Fin n → ℂ, prodFun g y *
    (Set.Ioi (0 : ℝ)).indicator g (sgn ℝ (ε 0) * (t - qEps (fun i => ε ((0 : Fin (n + 1)).succAbove i)) y))

theorem prodFun_exp {n : ℕ} (y : Fin n → ℂ) : prodFun (fun r => Real.exp (-r)) y = gauss y := by
  simp only [prodFun, gauss, ← Real.exp_sum, Finset.sum_neg_distrib]

theorem sgn_mul_self (s : Bool) : sgn ℝ s * sgn ℝ s = 1 := by cases s <;> simp [sgn]

theorem abs_sgn (s : Bool) : |sgn ℝ s| = 1 := by cases s <;> simp [sgn]

theorem measurePreserving_sgn (s : Bool) (c : ℝ) :
    MeasurePreserving (fun t : ℝ => sgn ℝ s * (t - c)) volume volume := by
  cases s
  · have := (Measure.measurePreserving_neg (volume : Measure ℝ)).comp (measurePreserving_sub_right volume c)
    simpa [sgn, Function.comp_def] using this
  · simpa [sgn] using measurePreserving_sub_right (volume : Measure ℝ) c

theorem integral_sgn (s : Bool) (c : ℝ) (f : ℝ → ℝ) : ∫ t, f (sgn ℝ s * (t - c)) = ∫ r, f r := by
  rw [integral_sub_right_eq_self (fun t => f (sgn ℝ s * t)) c, Measure.integral_comp_mul_left, abs_inv, abs_sgn]
  simp

section

variable {g : ℝ → ℝ} (hc : Continuous g) (h0 : ∀ r, 0 ≤ g r) (h1 : ∀ r, g r ≤ Real.exp (-r))

include hc in
theorem continuous_prodFun (n : ℕ) : Continuous (prodFun g : (Fin n → ℂ) → ℝ) := by
  unfold prodFun; fun_prop

include h0 in
theorem prodFun_nonneg {n : ℕ} (y : Fin n → ℂ) : 0 ≤ prodFun g y := Finset.prod_nonneg fun _ _ => h0 _

include h0 h1 in
theorem prodFun_le {n : ℕ} (y : Fin n → ℂ) : prodFun g y ≤ gauss y := by
  rw [← prodFun_exp]
  exact Finset.prod_le_prod (fun _ _ => h0 _) fun _ _ => h1 _

include hc h0 h1 in
theorem integrable_prodFun (n : ℕ) : Integrable (prodFun g : (Fin n → ℂ) → ℝ) :=
  (integrable_gauss n).mono' (continuous_prodFun hc n).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (prodFun_nonneg h0 y)]; exact prodFun_le h0 h1 y)

include hc h0 h1 in
theorem integrable_cut : Integrable ((Set.Ioi (0 : ℝ)).indicator g) := by
  rw [integrable_indicator_iff measurableSet_Ioi]
  exact Integrable.mono' (integrableOn_exp_neg_Ioi 0) hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun r => by rw [Real.norm_of_nonneg (h0 r)]; exact h1 r)

include h0 h1 in
theorem norm_term_le {n : ℕ} (y : Fin n → ℂ) (r : ℝ) :
    ‖prodFun g y * (Set.Ioi (0 : ℝ)).indicator g r‖ ≤ gauss y := by
  rw [norm_mul, Real.norm_of_nonneg (prodFun_nonneg h0 y)]
  refine (mul_le_of_le_one_right (prodFun_nonneg h0 y) ?_).trans (prodFun_le h0 h1 y)
  by_cases hr : r ∈ Set.Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem hr, Real.norm_of_nonneg (h0 r)]
    exact (h1 r).trans (Real.exp_le_one_iff.2 (neg_nonpos.2 (le_of_lt hr)))
  · simp [Set.indicator_of_notMem hr]

include hc in
theorem measurable_term {n : ℕ} (ε : Fin n → Bool) (s : Bool) (t : ℝ) : Measurable fun y : Fin n → ℂ =>
    prodFun g y * (Set.Ioi (0 : ℝ)).indicator g (sgn ℝ s * (t - qEps ε y)) :=
  (continuous_prodFun hc n).measurable.mul ((hc.measurable.indicator measurableSet_Ioi).comp
    (measurable_const.mul (measurable_const.sub (continuous_qEps ε).measurable)))

include hc h0 h1 in
theorem integrable_shear {n : ℕ} (ε : Fin n → Bool) (s : Bool) : Integrable (fun p : (Fin n → ℂ) × ℝ =>
    prodFun g p.1 * (Set.Ioi (0 : ℝ)).indicator g (sgn ℝ s * (p.2 - qEps ε p.1))) (volume.prod volume) := by
  have hq := continuous_qEps ε
  have hp : MeasurePreserving (fun p : (Fin n → ℂ) × ℝ => (id p.1, sgn ℝ s * (p.2 - qEps ε p.1)))
      (volume.prod volume) (volume.prod volume) :=
    (MeasurePreserving.id volume).skew_product (g := fun y t => sgn ℝ s * (t - qEps ε y))
      (by apply Continuous.measurable; unfold Function.uncurry; fun_prop)
      (Filter.Eventually.of_forall fun y => (measurePreserving_sgn s _).map_eq)
  exact hp.integrable_comp_of_integrable ((integrable_prodFun hc h0 h1 n).mul_prod (integrable_cut hc h0 h1))

include hc h0 h1 in
theorem integrable_dens {n : ℕ} (ε : Fin (n + 1) → Bool) : Integrable (dens g ε) :=
  (integrable_shear hc h0 h1 _ (ε 0)).integral_prod_right.const_mul _

include hc h0 h1 in
theorem setIntegral_eq {n : ℕ} (ε : Fin (n + 1) → Bool) {S : Set ℝ} (hS : MeasurableSet S) :
    ∫ y in {y | qEps ε y ∈ S}, prodFun g y = ∫ t in S, dens g ε t := by
  set ε' : Fin n → Bool := fun i => ε ((0 : Fin (n + 1)).succAbove i) with hε'
  have hm : MeasurableSet {y : Fin (n + 1) → ℂ | qEps ε y ∈ S} := (continuous_qEps ε).measurable hS
  have hp := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) 0).symm
  have hi := (integrable_prodFun hc h0 h1 (n + 1)).indicator hm
  have hi' := (hp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hi
  have hs : Integrable (Function.uncurry fun (y : Fin n → ℂ) (t : ℝ) =>
      prodFun g y * (Set.Ioi (0 : ℝ)).indicator g (sgn ℝ (ε 0) * (t - qEps ε' y)))
      (volume.prod (volume.restrict S)) := by
    have := (integrable_shear hc h0 h1 ε' (ε 0)).integrableOn (s := Set.univ ×ˢ S)
    rwa [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ] at this
  rw [← integral_indicator hm, ← hp.integral_comp']
  refine (integral_prod_symm _ hi').trans ?_
  unfold dens
  rw [integral_const_mul, ← integral_integral_swap hs, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have e1 := integral_norm_sq fun r => S.indicator (fun _ => prodFun g y * g r) (sgn ℝ (ε 0) * r + qEps ε' y)
  have e2 := integral_sgn (ε 0) (qEps ε' y) ((Set.Ioi (0 : ℝ)).indicator
    fun r => S.indicator (fun _ => prodFun g y * g r) (sgn ℝ (ε 0) * r + qEps ε' y))
  rw [← integral_indicator measurableSet_Ioi, ← e2] at e1
  beta_reduce
  rw [← integral_indicator hS]
  refine Eq.trans ?_ (e1.trans ?_)
  · refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    set w := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) 0).symm (z, y) with hw
    have a1 : qEps ε w = sgn ℝ (ε 0) * ‖z‖ ^ 2 + qEps ε' y := by
      simp only [hw, qEps, Fin.sum_univ_succAbove _ (0 : Fin (n + 1)), hε',
        MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_apply_same,
        Fin.insertNth_apply_succAbove, sgn]
    have a2 : prodFun g w = prodFun g y * g (‖z‖ ^ 2) := by
      simp only [hw, prodFun, Fin.prod_univ_succAbove _ (0 : Fin (n + 1)),
        MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_apply_same,
        Fin.insertNth_apply_succAbove]
      rw [mul_comm]
    show Set.indicator _ _ w = _
    beta_reduce
    rw [← a1, ← a2]
    rfl
  · congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    have a : sgn ℝ (ε 0) * (sgn ℝ (ε 0) * (t - qEps ε' y)) + qEps ε' y = t := by
      rw [← mul_assoc, sgn_mul_self]; ring
    by_cases b1 : sgn ℝ (ε 0) * (t - qEps ε' y) ∈ Set.Ioi (0 : ℝ) <;> by_cases b2 : t ∈ S <;>
      simp only [Set.indicator_of_mem, Set.indicator_of_notMem, a, b1, b2, not_false_eq_true, mul_zero]

end

theorem ae_qEps_ne : ∀ {n : ℕ} (ε : Fin n → Bool) {t : ℝ}, t ≠ 0 → ∀ᵐ y : Fin n → ℂ, qEps ε y ≠ t
  | 0, ε, t, ht => Filter.Eventually.of_forall fun y => by simpa [qEps] using ht.symm
  | n + 1, ε, t, _ => by
      have h := setIntegral_eq (g := fun r => Real.exp (-r)) (by fun_prop) (fun _ => (Real.exp_pos _).le)
        (fun _ => le_rfl) ε (measurableSet_singleton t)
      simp only [prodFun_exp, Measure.restrict_singleton, measure_singleton, zero_smul, integral_zero_measure] at h
      have h2 := (setIntegral_pos_iff_support_of_nonneg_ae (s := {y | qEps ε y ∈ ({t} : Set ℝ)})
        (Filter.Eventually.of_forall fun y => (gauss_pos y).le) (integrable_gauss (n + 1)).integrableOn).not.1
        (by rw [h]; exact lt_irrefl _)
      rw [ae_iff]
      refine measure_mono_null (fun y hy => ?_) (nonpos_iff_eq_zero.1 (not_lt.1 h2))
      exact ⟨(gauss_pos y).ne', by simpa using hy⟩

theorem continuousAt_dens {g : ℝ → ℝ} (hc : Continuous g) (h0 : ∀ r, 0 ≤ g r) (h1 : ∀ r, g r ≤ Real.exp (-r))
    {n : ℕ} (ε : Fin (n + 1) → Bool) {t : ℝ} (ht : t ≠ 0) : ContinuousAt (dens g ε) t := by
  refine continuousAt_const.mul (continuousAt_of_dominated (bound := gauss)
    (Filter.Eventually.of_forall fun u => (measurable_term hc _ _ u).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun u => Filter.Eventually.of_forall fun y => norm_term_le h0 h1 y _)
    (integrable_gauss n) ?_)
  filter_upwards [ae_qEps_ne (fun i => ε ((0 : Fin (n + 1)).succAbove i)) ht] with y hy
  refine continuousAt_const.mul (ContinuousAt.comp (g := (Set.Ioi (0 : ℝ)).indicator g)
    (f := fun u : ℝ => sgn ℝ (ε 0) * (u - qEps (fun i => ε ((0 : Fin (n + 1)).succAbove i)) y)) ?_ (by fun_prop))
  refine hc.continuousOn.continuousAt_indicator ?_
  rw [frontier_Ioi, Set.mem_singleton_iff]
  refine mul_ne_zero ?_ (sub_ne_zero.2 hy.symm)
  unfold sgn; split_ifs <;> simp

theorem isDens_prodFun {g : ℝ → ℝ} (hc : Continuous g) (h0 : ∀ r, 0 ≤ g r) (h1 : ∀ r, g r ≤ Real.exp (-r))
    {n : ℕ} (ε : Fin (n + 1) → Bool) : IsDens ε (prodFun g) (dens g ε) :=
  ⟨fun _ ht => (continuousAt_dens hc h0 h1 ε ht).continuousWithinAt,
    fun _ hS _ => setIntegral_eq hc h0 h1 ε hS.measurableSet⟩

theorem gaussDens_eq {n : ℕ} (ε : Fin (n + 1) → Bool) {t : ℝ} (ht : t ≠ 0) :
    gaussDens ε t = dens (fun r => Real.exp (-r)) ε t := by
  have hc : Continuous fun r : ℝ => Real.exp (-r) := by fun_prop
  have h0 : ∀ r : ℝ, 0 ≤ Real.exp (-r) := fun _ => (Real.exp_pos _).le
  have hi := integrable_dens hc h0 (fun _ => le_rfl) ε
  have h1 : (fun s : ℝ => ∫ y in {y : Fin (n + 1) → ℂ | qEps ε y ≤ s}, gauss y) =
      fun s => (∫ u in Set.Iic t, dens (fun r => Real.exp (-r)) ε u) +
        ∫ u in t..s, dens (fun r => Real.exp (-r)) ε u := by
    funext s
    have h := setIntegral_eq hc h0 (fun _ => le_rfl) ε (measurableSet_Iic (a := s))
    simp only [prodFun_exp, Set.mem_Iic] at h
    rw [h, ← intervalIntegral.integral_Iic_sub_Iic hi.integrableOn hi.integrableOn]; ring
  rw [gaussDens, h1]
  exact (HasDerivAt.const_add _ (intervalIntegral.integral_hasDerivAt_right (by simp)
    hi.aestronglyMeasurable.stronglyMeasurableAtFilter (continuousAt_dens hc h0 (fun _ => le_rfl) ε ht))).deriv

def cutExp (k : ℕ) (r : ℝ) : ℝ := Real.smoothTransition (k + 1 - r) * Real.exp (-r)

theorem contDiff_cutExp (k : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cutExp k) :=
  (Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)).mul (Real.contDiff_exp.comp contDiff_neg)

theorem cutExp_nonneg (k : ℕ) (r : ℝ) : 0 ≤ cutExp k r :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.exp_pos _).le

theorem cutExp_le (k : ℕ) (r : ℝ) : cutExp k r ≤ Real.exp (-r) :=
  mul_le_of_le_one_left (Real.exp_pos _).le (Real.smoothTransition.le_one _)

theorem cutExp_mono (r : ℝ) : Monotone fun k => cutExp k r := fun a b h =>
  mul_le_mul_of_nonneg_right (Real.smoothTransition.monotone (by
    have : (a : ℝ) ≤ b := by exact_mod_cast h
    linarith)) (Real.exp_pos _).le

theorem tendsto_cutExp (r : ℝ) : Filter.Tendsto (fun k => cutExp k r) Filter.atTop (nhds (Real.exp (-r))) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop ⌈r⌉₊] with k hk
  have := Nat.ceil_le.1 hk
  rw [cutExp, Real.smoothTransition.one_of_one_le (by linarith), one_mul]

theorem tendsto_prodFun {n : ℕ} (y : Fin n → ℂ) : Filter.Tendsto (fun k => prodFun (cutExp k) y) Filter.atTop
    (nhds (prodFun (fun r => Real.exp (-r)) y)) :=
  tendsto_finset_prod _ fun _ _ => tendsto_cutExp _

theorem hasCompactSupport_prodFun (k n : ℕ) : HasCompactSupport (prodFun (cutExp k) : (Fin n → ℂ) → ℝ) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin n → ℂ) (k + 1)) fun y hy => ?_
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by linarith)] at hy
  push_neg at hy
  obtain ⟨i, hi⟩ := hy
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  rw [cutExp, Real.smoothTransition.zero_of_nonpos (by nlinarith), zero_mul]

theorem contDiff_prodFun (k n : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (prodFun (cutExp k) : (Fin n → ℂ) → ℝ) :=
  contDiff_prod fun i _ => (contDiff_cutExp k).comp ((contDiff_apply ℝ ℂ i).norm_sq ℂ)

theorem tendsto_dens {n : ℕ} (ε : Fin (n + 1) → Bool) (t : ℝ) :
    Filter.Tendsto (fun k => dens (cutExp k) ε t) Filter.atTop (nhds (dens (fun r => Real.exp (-r)) ε t)) := by
  refine Filter.Tendsto.const_mul _ (tendsto_integral_of_dominated_convergence gauss
    (fun k => (measurable_term (contDiff_cutExp k).continuous _ _ t).aestronglyMeasurable) (integrable_gauss n)
    (fun k => Filter.Eventually.of_forall fun y => norm_term_le (cutExp_nonneg k) (cutExp_le k) y _)
    (Filter.Eventually.of_forall fun y => (tendsto_prodFun y).mul ?_))
  simp only [Set.indicator]
  split_ifs
  · exact tendsto_cutExp _
  · exact tendsto_const_nhds

theorem exists_truncated (n : ℕ) (ε : Fin n → Bool) :
    ∃ (φ : ℕ → (Fin n → ℂ) → ℝ) (D : ℕ → ℝ → ℝ),
      (∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ k) ∧ HasCompactSupport (φ k) ∧ (∀ y, 0 ≤ φ k y) ∧
        IsDens ε (φ k) (D k)) ∧
      (∀ y, Monotone (fun k => φ k y) ∧ Filter.Tendsto (fun k => φ k y) Filter.atTop (nhds (gauss y))) ∧
      ∀ β : ℝ, β ≠ 0 → Filter.Tendsto (fun k => D k β) Filter.atTop (nhds (gaussDens ε β)) := by
  have key : ∀ y : Fin n → ℂ, Monotone (fun k => prodFun (cutExp k) y) ∧
      Filter.Tendsto (fun k => prodFun (cutExp k) y) Filter.atTop (nhds (gauss y)) := fun y =>
    ⟨fun _ _ h => Finset.prod_le_prod (fun _ _ => cutExp_nonneg _ _) fun _ _ => cutExp_mono _ h,
      prodFun_exp y ▸ tendsto_prodFun y⟩
  obtain _ | n := n
  · refine ⟨fun k => prodFun (cutExp k), fun _ _ => 0, fun k => ⟨contDiff_prodFun k 0,
      hasCompactSupport_prodFun k 0, prodFun_nonneg (cutExp_nonneg k), continuousOn_const, fun S _ hS => ?_⟩,
      key, fun β hβ => ?_⟩
    · have : {y : Fin 0 → ℂ | qEps ε y ∈ S} = ∅ :=
        Set.eq_empty_of_forall_notMem fun y hy => hS hy (by simp [qEps])
      simp [this]
    · have : gaussDens ε β = 0 := by
        show deriv (cdf ε) β = 0
        rw [(cdf_zero_eventually ε hβ).deriv_eq]; simp
      rw [this]; exact tendsto_const_nhds
  · refine ⟨fun k => prodFun (cutExp k), fun k => dens (cutExp k) ε, fun k => ⟨contDiff_prodFun k _,
      hasCompactSupport_prodFun k _, prodFun_nonneg (cutExp_nonneg k),
      isDens_prodFun (contDiff_cutExp k).continuous (cutExp_nonneg k) (cutExp_le k) ε⟩, key, fun β hβ => ?_⟩
    rw [gaussDens_eq ε hβ]
    exact tendsto_dens ε β

end GlobalTheory.GaussMean.Trunc
