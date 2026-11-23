import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation

noncomputable section

open MeasureTheory Complex SchwartzMap Matrix Filter Topology Asymptotics
open scoped Real RealInnerProductSpace ContDiff

namespace PositivityTheory.RL.Up

open GlobalTheory.RealWeil

theorem bdd_of_weak {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] (h : ℝ → B)
    (hc : ∀ φ : B →L[ℂ] ℂ, Continuous fun t => φ (h t)) : ∃ M, ∀ t ∈ Set.Icc (-1 : ℝ) 1, ‖h t‖ ≤ M := by
  obtain ⟨C, hC⟩ := banach_steinhaus (g := fun t : Set.Icc (-1 : ℝ) 1 => NormedSpace.inclusionInDoubleDual ℂ B (h t))
    fun φ => by
      obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc φ).continuousOn
      exact ⟨C, fun t => hC t t.2⟩
  refine ⟨C, fun t ht => ?_⟩
  have := hC ⟨t, ht⟩
  rwa [show ‖NormedSpace.inclusionInDoubleDual ℂ B (h t)‖ = ‖h t‖ from
    (NormedSpace.inclusionInDoubleDualLi ℂ (E := B)).norm_map (h t)] at this

theorem taylor2 (φ φ' φ'' : ℝ → ℂ) (h1 : ∀ t, HasDerivAt φ (φ' t) t) (h2 : ∀ t, HasDerivAt φ' (φ'' t) t) {M : ℝ}
    (hM : ∀ t ∈ Set.Icc (-1 : ℝ) 1, ‖φ'' t‖ ≤ M) {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    ‖φ t - φ 0 - t * φ' 0‖ ≤ M * t ^ 2 := by
  have h0 : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by norm_num
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 h0)
  have a1 : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ‖φ' u - φ' 0‖ ≤ M * ‖u - 0‖ := fun u hu =>
    (convex_Icc (-1 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le (fun x _ => (h2 x).hasDerivWithinAt) hM h0 hu
  have hsub : Set.uIcc 0 t ⊆ Set.Icc (-1 : ℝ) 1 := Set.uIcc_subset_Icc h0 ht
  have a2 := (convex_uIcc (0 : ℝ) t).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun u : ℝ => φ u - u * φ' 0) (f' := fun u => φ' u - φ' 0) (C := M * |t|)
    (fun x _ => ((h1 x).sub ((((hasDerivAt_id x).ofReal_comp).mul_const (φ' 0)).congr_deriv (by simp))).hasDerivWithinAt)
    (fun u hu => (a1 u (hsub hu)).trans (by
      rw [sub_zero, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (by simpa using Set.abs_sub_left_of_mem_uIcc hu) hM0))
    Set.left_mem_uIcc Set.right_mem_uIcc
  rw [sub_zero, Real.norm_eq_abs, mul_assoc, abs_mul_abs_self, ← sq] at a2
  refine le_trans (le_of_eq (congrArg norm ?_)) a2
  push_cast
  ring

theorem norm_le_of_avg {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
    [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (g : V → ℂ) (hg : Continuous g) {C : ℝ} (x : V)
    (h : ∀ r > 0, ‖∫ y in Metric.closedBall x r, g y ∂μ‖ ≤ C * μ.real (Metric.closedBall x r)) : ‖g x‖ ≤ C := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.1 (hg.continuousAt (x := x)) ε hε
  have hr : 0 < δ / 2 := by positivity
  set s := Metric.closedBall x (δ / 2)
  have hfin : μ s < ⊤ := (isCompact_closedBall x _).measure_lt_top
  have hpos : 0 < μ.real s := ENNReal.toReal_pos (Metric.measure_closedBall_pos μ x hr).ne' hfin.ne
  have h1 : ‖∫ y in s, (g x - g y) ∂μ‖ ≤ ε * μ.real s :=
    norm_setIntegral_le_of_norm_le_const hfin fun y hy => by
      rw [← dist_eq_norm, dist_comm]
      exact (hd (lt_of_le_of_lt (Metric.mem_closedBall.1 hy) (by linarith))).le
  rw [integral_sub (show IntegrableOn (fun _ => g x) s μ from integrableOn_const hfin.ne) (hg.continuousOn.integrableOn_compact (isCompact_closedBall x _)),
    setIntegral_const] at h1
  have h2 := h _ hr
  have h3 : ‖μ.real s • g x‖ ≤ (C + ε) * μ.real s := by
    have := norm_add_le (μ.real s • g x - ∫ y in s, g y ∂μ) (∫ y in s, g y ∂μ)
    rw [sub_add_cancel] at this
    linarith
  rw [norm_smul, Real.norm_of_nonneg hpos.le, mul_comm] at h3
  exact le_of_mul_le_mul_right h3 hpos

variable {l : Type} [Fintype l] [DecidableEq l]

def Good {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] (U : ℝ → (Sch l →L[ℂ] Sch l)) (Q : Sch l →L[ℂ] Sch l)
    (j : Sch l →L[ℂ] B) : Prop := ∀ f, HasDerivAt (fun t => j (U t f)) (j (Q f)) 0

omit [DecidableEq l] in
theorem good_sup (U : ℝ → (Sch l →L[ℂ] Sch l)) (Q : Sch l →L[ℂ] Sch l) (h0 : U 0 = 1)
    (hm : ∀ s t, U (s + t) = U s * U t)
    (h1 : ∀ f, HasDerivAt (fun t => (U t f).toLp 2 volume) ((Q f).toLp 2 volume) 0)
    (hL : ∀ s, ∃ L : L2 l →L[ℂ] L2 l, ∀ f, (U s f).toLp 2 volume = L (f.toLp 2 volume))
    (hw : ∀ (T : Sch l →L[ℂ] ℂ) f, Continuous fun t => T (U t f)) :
    Good U Q (toBoundedContinuousFunctionCLM ℂ _ ℂ) := by
  intro f
  have hd : ∀ g s, HasDerivAt (fun t => (U t g).toLp 2 volume) ((U s (Q g)).toLp 2 volume) s := fun g s => by
    obtain ⟨L, hL⟩ := hL s
    have a : HasDerivAt (fun t => (U (t - s) g).toLp 2 volume) ((Q g).toLp 2 volume) s := by
      have := h1 g
      rw [← sub_self s] at this
      exact this.comp_sub_const s s
    have b := (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s a
    rw [hL]
    refine b.congr_of_eventuallyEq (.of_forall fun t => ?_)
    show _ = L _
    rw [← hL, ← ContinuousLinearMap.mul_apply, ← hm, add_sub_cancel]
  obtain ⟨M, hM⟩ := bdd_of_weak (fun t => toBoundedContinuousFunctionCLM ℂ _ ℂ (U t (Q (Q f))))
    fun φ => hw (φ ∘L toBoundedContinuousFunctionCLM ℂ _ ℂ) _
  have key : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      ‖toBoundedContinuousFunctionCLM ℂ _ ℂ (U t f - f - (t : ℂ) • Q f)‖ ≤ M * t ^ 2 := fun t ht => by
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by norm_num))
    refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun x => ?_
    refine norm_le_of_avg volume (U t f - f - (t : ℂ) • Q f : Sch l) (SchwartzMap.continuous _) x fun r hr => ?_
    set s := Metric.closedBall x r
    have hfin : volume s < ⊤ := (isCompact_closedBall x _).measure_lt_top
    let u : L2 l := indicatorConstLp 2 (measurableSet_closedBall (x := x) (ε := r)) hfin.ne (1 : ℂ)
    have hu : ∀ g : Sch l, innerSL ℂ u (g.toLp 2 volume) = ∫ y in s, g y := fun g => by
      rw [innerSL_apply_apply, L2.inner_indicatorConstLp_one]
      exact setIntegral_congr_ae measurableSet_closedBall ((g.coeFn_toLp 2 volume).mono fun y hy _ => hy)
    have hd' : ∀ g s, HasDerivAt (fun t => innerSL ℂ u ((U t g).toLp 2 volume))
        (innerSL ℂ u ((U s (Q g)).toLp 2 volume)) s := fun g s =>
      ((innerSL ℂ u).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s (hd g s)
    have := taylor2 _ _ _ (hd' f) (hd' (Q f)) (M := M * volume.real s) (fun v hv => by
      rw [hu]
      exact norm_setIntegral_le_of_norm_le_const hfin fun y _ =>
        (BoundedContinuousFunction.norm_coe_le_norm (toBoundedContinuousFunctionCLM ℂ _ ℂ (U v (Q (Q f)))) y).trans
          (hM v hv)) ht
    rw [← hu]
    simp only [h0, ContinuousLinearMap.one_apply] at this
    rw [← toLpCLM_apply (𝕜 := ℂ), map_sub, map_sub, map_smul, map_sub, map_sub, map_smul]
    simp only [toLpCLM_apply, smul_eq_mul]
    linarith
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  refine IsBigO.trans_isLittleO (g := fun t : ℝ => t ^ 2) (IsBigO.of_bound M ?_) (isLittleO_pow_id (by norm_num))
  filter_upwards [Icc_mem_nhds (show (-1 : ℝ) < 0 by norm_num) (show (0 : ℝ) < 1 by norm_num)] with t ht
  have := key t ht
  simp only [map_sub, map_smul] at this
  simpa [h0, ← Complex.coe_smul] using this

theorem good_mul {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] (U : ℝ → (Sch l →L[ℂ] Sch l))
    (Q : Sch l →L[ℂ] Sch l) (h0 : U 0 = 1) (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) (c : ℝ → (l ⊕ l → ℝ) → (l ⊕ l → ℝ))
    (hc0 : ∀ w, c 0 w = w) (hc : ∀ w a, HasDerivAt (fun t => c t w a) (-(X *ᵥ w) a) 0)
    (hD : ∀ t w, dRho w * U t = U t * dRho (c t w))
    (hQ : ∀ w, Q * dRho w - dRho w * Q = dRho (X *ᵥ w)) {j : Sch l →L[ℂ] B} (hj : Good U Q j) (w : l ⊕ l → ℝ) :
    Good U Q (j ∘L dRho w) := by
  intro f
  have e : (fun t => (j ∘L dRho w) (U t f)) = fun t => ∑ a, ((c t w a : ℝ) : ℂ) • j (U t (dRho (Pi.single a 1) f)) := by
    funext t
    show j ((dRho w * U t) f) = _
    rw [hD, ContinuousLinearMap.mul_apply, dRho_eq_sum]
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, map_sum, map_smul]
  rw [e]
  have := HasDerivAt.fun_sum (u := Finset.univ) fun a _ => ((hc w a).ofReal_comp).smul (hj (dRho (Pi.single a 1) f))
  refine this.congr_deriv ?_
  simp only [h0, hc0, ContinuousLinearMap.one_apply, Finset.sum_add_distrib]
  have e1 : dRho w * Q = Q * dRho w - dRho (X *ᵥ w) := by rw [← hQ]; abel
  show _ = j ((dRho w * Q) f)
  rw [e1, ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply, map_sub, dRho_eq_sum w, dRho_eq_sum (X *ᵥ w)]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, map_sum, map_smul, ofReal_neg, neg_smul,
    Finset.sum_neg_distrib, sub_eq_add_neg]

theorem seminorm_succ_n (k n : ℕ) (g : Sch l) :
    SchwartzMap.seminorm ℂ k (n + 1) g ≤ ∑ i, SchwartzMap.seminorm ℂ k n (dRho (Pi.single (Sum.inl i) 1) g) := by
  refine SchwartzMap.seminorm_le_bound ℂ k (n + 1) g (Finset.sum_nonneg fun _ _ => apply_nonneg _ _) fun x => ?_
  let L : l → ℂ →L[ℝ] (EuclideanSpace ℝ l →L[ℝ] ℂ) := fun i =>
    ContinuousLinearMap.smulRightL ℝ _ ℂ (EuclideanSpace.proj i)
  have hL : ∀ i, ‖L i‖ ≤ 1 := fun i => ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => by
    rw [one_mul]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
    show ‖(v i) • z‖ ≤ _
    rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le v i) (norm_nonneg _)
  have e : fderiv ℝ g = fun y => ∑ i, (L i ∘ dRho (Pi.single (Sum.inl i) 1) g) y := by
    funext y
    ext v
    have hv : v = ∑ i, v i • (EuclideanSpace.single i 1 : EuclideanSpace ℝ l) := by
      ext j
      simp [Pi.single_apply]
    conv_lhs => rw [hv]
    simp [L, dRho_single_inl, lineDerivOp_apply_eq_fderiv]
  have hs : ∀ i, ContDiff ℝ ∞ (dRho (Pi.single (Sum.inl i) 1) g : Sch l) := fun i => SchwartzMap.smooth _ ⊤
  rw [← norm_iteratedFDeriv_fderiv, e, iteratedFDeriv_fun_sum_apply (fun i _ =>
    (((L i).contDiff.comp (hs i)).of_le (by exact_mod_cast le_top)).contDiffAt)]
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => le_trans ?_ (SchwartzMap.le_seminorm ℂ k n _ x)
  refine mul_le_mul_of_nonneg_left (((L i).norm_iteratedFDeriv_comp_left (hs i).contDiffAt
    (by exact_mod_cast le_top)).trans ?_) (by positivity)
  exact mul_le_of_le_one_left (norm_nonneg _) (hL i)

theorem seminorm_succ_k (k : ℕ) (g : Sch l) :
    SchwartzMap.seminorm ℂ (k + 1) 0 g ≤ ∑ i, SchwartzMap.seminorm ℂ k 0 (dRho (Pi.single (Sum.inr i) 1) g) := by
  refine SchwartzMap.seminorm_le_bound ℂ (k + 1) 0 g (Finset.sum_nonneg fun _ _ => apply_nonneg _ _) fun x => ?_
  have h1 : ‖x‖ ≤ ∑ i, |x i| := by
    have hv : x = ∑ i, x i • (EuclideanSpace.single i 1 : EuclideanSpace ℝ l) := by
      ext j
      simp [Pi.single_apply]
    conv_lhs => rw [hv]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    simp [norm_smul]
  rw [norm_iteratedFDeriv_zero]
  calc ‖x‖ ^ (k + 1) * ‖g x‖ = ‖x‖ * (‖x‖ ^ k * ‖g x‖) := by ring
    _ ≤ (∑ i, |x i|) * (‖x‖ ^ k * ‖g x‖) := mul_le_mul_of_nonneg_right h1 (by positivity)
    _ ≤ _ := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => le_trans ?_ (SchwartzMap.le_seminorm ℂ k 0 _ x)
      rw [norm_iteratedFDeriv_zero, dRho_single_inr]
      simp only [norm_mul, norm_ofNat, norm_real, norm_I, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      have : |x i| * (‖x‖ ^ k * ‖g x‖) * 1 ≤ |x i| * (‖x‖ ^ k * ‖g x‖) * (2 * π) :=
        mul_le_mul_of_nonneg_left (by linarith [Real.pi_gt_three]) (by positivity)
      linarith

theorem weak_deriv (U : ℝ → (Sch l →L[ℂ] Sch l)) (Q : Sch l →L[ℂ] Sch l) (h0 : U 0 = 1)
    (hj : Good U Q (toBoundedContinuousFunctionCLM ℂ _ ℂ))
    (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) (c : ℝ → (l ⊕ l → ℝ) → (l ⊕ l → ℝ))
    (hc0 : ∀ w, c 0 w = w) (hc : ∀ w a, HasDerivAt (fun t => c t w a) (-(X *ᵥ w) a) 0)
    (hD : ∀ t w, dRho w * U t = U t * dRho (c t w))
    (hQ : ∀ w, Q * dRho w - dRho w * Q = dRho (X *ᵥ w)) (T : Sch l →L[ℂ] ℂ) : Good U Q T := by
  intro f
  let W := Submonoid.closure (Set.range (dRho (l := l)))
  let R : ℝ → Sch l := fun t => U t f - f - (t : ℂ) • Q f
  have hW : ∀ L ∈ W, Good U Q (toBoundedContinuousFunctionCLM ℂ _ ℂ ∘L L) := fun L hL => by
    induction hL using Submonoid.closure_induction_right with
    | one => exact hj
    | mul_right x _ y hy ih =>
      obtain ⟨w, rfl⟩ := hy
      exact good_mul U Q h0 X c hc0 hc hD hQ ih w
  have hDW : ∀ w, ∀ L ∈ W, dRho w * L ∈ W := fun w L hL => mul_mem (Submonoid.subset_closure ⟨w, rfl⟩) hL
  have hk : ∀ k, ∀ L ∈ W, (fun t => SchwartzMap.seminorm ℂ k 0 (L (R t))) =o[𝓝 0] fun t => t := fun k => by
    induction k with
    | zero =>
      intro L hL
      have := hasDerivAt_iff_isLittleO_nhds_zero.1 (hW L hL f)
      refine IsBigO.trans_isLittleO (IsBigO.of_bound 1 (.of_forall fun t => ?_)) this
      rw [one_mul, Real.norm_of_nonneg (apply_nonneg _ _)]
      refine SchwartzMap.seminorm_le_bound ℂ 0 0 _ (norm_nonneg _) fun x => ?_
      rw [pow_zero, one_mul, norm_iteratedFDeriv_zero]
      refine le_trans (BoundedContinuousFunction.norm_coe_le_norm (toBoundedContinuousFunctionCLM ℂ _ ℂ (L (R t))) x)
        (le_of_eq ?_)
      simp [R, h0, ← Complex.coe_smul]
    | succ k ih =>
      intro L hL
      refine IsBigO.trans_isLittleO (IsBigO.of_bound 1 (.of_forall fun t => ?_))
        (IsLittleO.fun_sum (s := Finset.univ) fun i _ => ih _ (hDW (Pi.single (Sum.inr i) 1) L hL))
      rw [one_mul, Real.norm_of_nonneg (apply_nonneg _ _)]
      exact (seminorm_succ_k k _).trans (le_abs_self _)
  have hn : ∀ n k, ∀ L ∈ W, (fun t => SchwartzMap.seminorm ℂ k n (L (R t))) =o[𝓝 0] fun t => t := fun n => by
    induction n with
    | zero => exact hk
    | succ n ih =>
      intro k L hL
      refine IsBigO.trans_isLittleO (IsBigO.of_bound 1 (.of_forall fun t => ?_))
        (IsLittleO.fun_sum (s := Finset.univ) fun i _ => ih k _ (hDW (Pi.single (Sum.inl i) 1) L hL))
      rw [one_mul, Real.norm_of_nonneg (apply_nonneg _ _)]
      exact (seminorm_succ_n k n _).trans (le_abs_self _)
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ (EuclideanSpace ℝ l) ℂ)
    ((normSeminorm ℂ ℂ).comp T.toLinearMap) T.continuous.norm
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  refine IsBigO.trans_isLittleO (IsBigO.of_bound C (.of_forall fun t => ?_))
    (IsLittleO.fun_sum (s := s) fun i _ => hn i.2 i.1 1 (one_mem _))
  have h1 := hC (R t)
  have h2 : (s.sup (schwartzSeminormFamily ℂ (EuclideanSpace ℝ l) ℂ)) (R t) ≤
      ∑ i ∈ s, SchwartzMap.seminorm ℂ i.1 i.2 (R t) :=
    Seminorm.finset_sup_apply_le (Finset.sum_nonneg fun _ _ => apply_nonneg _ _) fun i hi =>
      Finset.single_le_sum (f := fun i : ℕ × ℕ => SchwartzMap.seminorm ℂ i.1 i.2 (R t)) (fun _ _ => apply_nonneg _ _) hi
  have h3 : ‖T (R t)‖ ≤ C * ∑ i ∈ s, SchwartzMap.seminorm ℂ i.1 i.2 (R t) :=
    h1.trans (mul_le_mul_of_nonneg_left h2 C.2)
  refine le_trans (le_of_eq ?_) (h3.trans (mul_le_mul_of_nonneg_left (le_abs_self _) C.2))
  simp [R, h0]

end PositivityTheory.RL.Up

end
