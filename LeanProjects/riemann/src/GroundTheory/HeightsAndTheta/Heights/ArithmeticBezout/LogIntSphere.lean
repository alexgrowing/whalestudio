import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LogIntPoly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Set MvPolynomial Matrix

noncomputable section

namespace HermNorm

variable {n : ℕ}

theorem li_norm_nonneg (h : HermNorm n) (v : Fin n → ℂ) : 0 ≤ h.norm v := Real.sqrt_nonneg _

theorem li_continuous_norm (h : HermNorm n) : Continuous h.norm := by
  unfold HermNorm.norm
  fun_prop

theorem li_norm_smul (h : HermNorm n) (a : ℂ) (v : Fin n → ℂ) :
    h.norm (fun j => a * v j) = ‖a‖ * h.norm v := by
  unfold HermNorm.norm
  have e : (h.mat *ᵥ fun j => a * v j) = fun i => a * (h.mat *ᵥ v) i := by
    have : (fun j => a * v j) = a • v := rfl
    rw [this, Matrix.mulVec_smul]
    rfl
  rw [e]
  simp_rw [norm_mul, mul_pow]
  rw [← Finset.mul_sum, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

theorem li_norm_mulVec_apply_le (h : HermNorm n) (v : Fin n → ℂ) (l : Fin n) :
    ‖(h.mat *ᵥ v) l‖ ≤ h.norm v := by
  unfold HermNorm.norm
  rw [← Real.sqrt_sq (_root_.norm_nonneg ((h.mat *ᵥ v) l))]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun i => ‖(h.mat *ᵥ v) i‖ ^ 2)
    (fun i _ => by positivity) (Finset.mem_univ l))

theorem li_inv_mulVec_mulVec (h : HermNorm n) (v : Fin n → ℂ) : h.mat⁻¹ *ᵥ (h.mat *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h.isUnit_det, Matrix.one_mulVec]

theorem li_exists_coord_le (h : HermNorm n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : Fin n → ℂ) (j : Fin n), ‖v j‖ ≤ C * h.norm v := by
  refine ⟨∑ j, ∑ l, ‖h.mat⁻¹ j l‖, by positivity, fun v j => ?_⟩
  conv_lhs => rw [← h.li_inv_mulVec_mulVec v]
  calc ‖(h.mat⁻¹ *ᵥ (h.mat *ᵥ v)) j‖ = ‖∑ l, h.mat⁻¹ j l * (h.mat *ᵥ v) l‖ := rfl
    _ ≤ ∑ l, ‖h.mat⁻¹ j l‖ * ‖(h.mat *ᵥ v) l‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp_rw [norm_mul]
    _ ≤ ∑ l, ‖h.mat⁻¹ j l‖ * h.norm v :=
        Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (h.li_norm_mulVec_apply_le v l)
          (_root_.norm_nonneg _)
    _ = (∑ l, ‖h.mat⁻¹ j l‖) * h.norm v := by rw [Finset.sum_mul]
    _ ≤ (∑ j, ∑ l, ‖h.mat⁻¹ j l‖) * h.norm v :=
        mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := fun j => ∑ l, ‖h.mat⁻¹ j l‖)
          (fun j _ => by positivity) (Finset.mem_univ j)) (h.li_norm_nonneg v)

theorem li_eq_zero_of_norm_eq_zero (h : HermNorm n) (v : Fin n → ℂ) (hv : h.norm v = 0) : v = 0 := by
  obtain ⟨C, -, hC⟩ := h.li_exists_coord_le
  funext j
  have := hC v j
  rw [hv, mul_zero] at this
  exact norm_le_zero_iff.mp this

theorem li_exists_mat_ne_zero (h : HermNorm n) (l : Fin n) : ∃ j, h.mat l j ≠ 0 := by
  by_contra hc
  push Not at hc
  exact h.isUnit_det.ne_zero (Matrix.det_eq_zero_of_row_eq_zero l hc)

end HermNorm

namespace LogInt

variable {n k : ℕ}

def inGroup (i : Fin k) : Fin k × Fin n → Prop := fun ij => ij.1 = i

instance (i : Fin k) : DecidablePred (inGroup (n := n) i) := fun ij => by
  unfold inGroup; infer_instance

def normT (h : HermNorm n) (T : Finset (Fin k)) (u : Fin k × Fin n → ℂ) : Fin k × Fin n → ℂ :=
  fun ij => if ij.1 ∈ T then ((h.norm fun j => u (ij.1, j) : ℝ) : ℂ)⁻¹ * u ij else u ij

theorem measurable_groupNorm (h : HermNorm n) (i : Fin k) :
    Measurable fun u : Fin k × Fin n → ℂ => h.norm fun j => u (i, j) :=
  h.li_continuous_norm.measurable.comp (measurable_pi_lambda _ fun _ => measurable_pi_apply _)

theorem measurable_normT (h : HermNorm n) (T : Finset (Fin k)) : Measurable (normT h T) := by
  refine measurable_pi_lambda _ fun ij => ?_
  by_cases hT : ij.1 ∈ T
  · simp only [normT, hT, if_true]
    exact (Complex.measurable_ofReal.comp (measurable_groupNorm h ij.1)).inv.mul
      (measurable_pi_apply _)
  · simp only [normT, hT, if_false]
    exact measurable_pi_apply _

theorem scale_inGroup_apply_same (i : Fin k) (c : ℂ) (u : Fin k × Fin n → ℂ) (j : Fin n) :
    scaleP (inGroup i) c u (i, j) = c * u (i, j) := by
  simp [scaleP, inGroup]

theorem scale_inGroup_apply_of_ne (i a : Fin k) (ha : a ≠ i) (c : ℂ) (u : Fin k × Fin n → ℂ) (j : Fin n) :
    scaleP (inGroup i) c u (a, j) = u (a, j) := by
  simp [scaleP, inGroup, ha]

theorem normT_scaleP (h : HermNorm n) (T : Finset (Fin k)) (i : Fin k) (θ : ℝ)
    (u : Fin k × Fin n → ℂ) :
    normT h T (scaleP (inGroup i) (circleMap 0 1 θ) u) =
      scaleP (inGroup i) (circleMap 0 1 θ) (normT h T u) := by
  funext ⟨a, b⟩
  by_cases hi : a = i
  · subst hi
    simp only [normT, h.li_norm_smul, norm_circleMap_zero, abs_one, one_mul, scale_inGroup_apply_same]
    split_ifs <;> ring
  ·     simp only [normT, scale_inGroup_apply_of_ne i a hi]

theorem normT_insert (h : HermNorm n) (T : Finset (Fin k)) (i : Fin k) (hi : i ∉ T)
    (u : Fin k × Fin n → ℂ) :
    normT h (insert i T) u =
      scaleP (inGroup i) ((h.norm fun j => u (i, j) : ℝ) : ℂ)⁻¹ (normT h T u) := by
  funext ij
  by_cases hij : ij.1 = i
  · have hT : ij.1 ∉ T := hij ▸ hi
    simp [normT, scaleP, inGroup, hij, hi]
  · simp [normT, scaleP, inGroup, hij]

theorem eval_scale_of_isWeightedHomogeneous {ι : Type*} (p : ι → Prop) [DecidablePred p] (a : ℂ) (v : ι → ℂ)
    (g : MvPolynomial ι ℂ) (d : ℕ) (hg : IsWeightedHomogeneous (indW p) g d) :
    eval (scaleP p a v) g = a ^ d * eval v g := by
  rw [eval_eq, eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [prod_scaleP, hg (mem_support_iff.mp hm)]
  ring

theorem normT_mem_polydisc (h : HermNorm n) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ (v : Fin n → ℂ) (j : Fin n), ‖v j‖ ≤ C * h.norm v) (T : Finset (Fin k))
    (u : Fin k × Fin n → ℂ) (hu : u ∈ polydisc _ C) : normT h T u ∈ polydisc _ C := by
  simp only [polydisc, mem_univ_pi, Metric.mem_closedBall, dist_zero_right] at hu ⊢
  intro ij
  by_cases hT : ij.1 ∈ T
  · simp only [normT, hT, if_true, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (h.li_norm_nonneg _)]
    by_cases h0 : (h.norm fun j => u (ij.1, j)) = 0
    · rw [h0, _root_.inv_zero, zero_mul]; exact hC0
    · rw [inv_mul_le_iff₀ (lt_of_le_of_ne (h.li_norm_nonneg _) (Ne.symm h0))]
      have := hC (fun j => u (ij.1, j)) ij.2
      simpa [mul_comm] using this
  · simp only [normT, hT, if_false]
    exact hu ij

theorem integrableOn_log_groupNorm (h : HermNorm n) (r : ℝ) (i : Fin k) :
    IntegrableOn (fun u : Fin k × Fin n → ℂ => Real.log (h.norm fun j => u (i, j)))
      (polydisc _ r) := by
  classical
  set ℓ : Fin n → MvPolynomial (Fin k × Fin n) ℂ := fun l => ∑ j, MvPolynomial.C (h.mat l j) * X (i, j)
    with hℓdef
  have hℓ : ∀ u l, eval u (ℓ l) = (h.mat *ᵥ fun j => u (i, j)) l := by
    intro u l
    simp [hℓdef, Matrix.mulVec, dotProduct]
  have hℓ0 : ∀ l, ℓ l ≠ 0 := by
    intro l h0
    obtain ⟨j, hj⟩ := h.li_exists_mat_ne_zero l
    have := congrArg (eval (fun ij : Fin k × Fin n => if ij = (i, j) then (1 : ℂ) else 0)) h0
    rw [hℓ, map_zero] at this
    simp [Matrix.mulVec, dotProduct] at this
    exact hj this
  obtain ⟨M, hM⟩ := (isCompact_polydisc (ι := Fin k × Fin n) r).exists_bound_of_continuousOn
    (f := fun u => h.norm fun j => u (i, j))
    (h.li_continuous_norm.comp (continuous_pi fun j => continuous_apply (i, j))).continuousOn
  refine Integrable.mono' (g := fun u => |Real.log (max M 1)| + ∑ l, |Real.log ‖eval u (ℓ l)‖|) ?_
    (Real.measurable_log.comp (measurable_groupNorm h i)).aestronglyMeasurable ?_
  · have : IsFiniteMeasure (volume.restrict (polydisc (Fin k × Fin n) r)) :=
      isFiniteMeasure_restrict.mpr (volume_polydisc_ne_top r)
    exact (integrable_const _).add (integrable_finsetSum _ fun l _ =>
      (integrableOn_log_norm_eval (ℓ l) (hℓ0 l) r).abs)
  · refine (ae_restrict_iff' (measurableSet_polydisc r)).mpr (Filter.Eventually.of_forall fun u hu => ?_)
    set N := h.norm fun j => u (i, j) with hN
    rw [Real.norm_eq_abs]
    have hS : 0 ≤ ∑ l, |Real.log ‖eval u (ℓ l)‖| := by positivity
    by_cases h0 : N = 0
    · rw [h0, Real.log_zero, abs_zero]; positivity
    · have hNpos : 0 < N := lt_of_le_of_ne (h.li_norm_nonneg _) (Ne.symm h0)
      have hup : Real.log N ≤ |Real.log (max M 1)| := by
        refine (Real.log_le_log hNpos ?_).trans (le_abs_self _)
        have := hM u hu
        rw [Real.norm_eq_abs, abs_of_nonneg (h.li_norm_nonneg _)] at this
        exact this.trans (le_max_left _ _)
      have hex : ∃ l, (h.mat *ᵥ fun j => u (i, j)) l ≠ 0 := by
        by_contra hc
        push Not at hc
        apply h0
        rw [hN]
        unfold HermNorm.norm
        simp [hc]
      obtain ⟨l, hl⟩ := hex
      have hlow : -∑ l, |Real.log ‖eval u (ℓ l)‖| ≤ Real.log N := by
        have h1 : Real.log ‖(h.mat *ᵥ fun j => u (i, j)) l‖ ≤ Real.log N :=
          Real.log_le_log (norm_pos_iff.mpr hl) (h.li_norm_mulVec_apply_le _ l)
        have h2 : |Real.log ‖eval u (ℓ l)‖| ≤ ∑ l, |Real.log ‖eval u (ℓ l)‖| :=
          Finset.single_le_sum (f := fun l => |Real.log ‖eval u (ℓ l)‖|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ l)
        rw [hℓ] at h2
        have h3 := neg_abs_le (Real.log ‖(h.mat *ᵥ fun j => u (i, j)) l‖)
        linarith
      rw [abs_le]
      constructor <;> linarith [abs_nonneg (Real.log (max M 1))]

theorem abs_log_inv_pow_mul_le (N : ℝ) (hN : 0 ≤ N) (d : ℕ) (x : ℂ) :
    |Real.log ‖((N : ℂ)⁻¹) ^ d * x‖| ≤ d * |Real.log N| + |Real.log ‖x‖| := by
  have hnn : 0 ≤ (d : ℝ) * |Real.log N| + |Real.log ‖x‖| := by positivity
  rw [norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hN]
  by_cases h0 : (N⁻¹) ^ d * ‖x‖ = 0
  · rw [h0, Real.log_zero, abs_zero]; exact hnn
  · rw [Real.log_mul (left_ne_zero_of_mul h0) (right_ne_zero_of_mul h0), Real.log_pow, Real.log_inv]
    refine (abs_add_le _ _).trans (le_of_eq ?_)
    rw [abs_mul, Nat.abs_cast, abs_neg]

theorem logNormT_insert_of_homog (h : HermNorm n) (r : ℝ) (T : Finset (Fin k)) (i : Fin k)
    (hi : i ∉ T) (g : MvPolynomial (Fin k × Fin n) ℂ) (hg : g ≠ 0) (d : ℕ)
    (hd : IsWeightedHomogeneous (indW (inGroup i)) g d)
    (ih1 : IntegrableOn (fun u => Real.log ‖eval (normT h T u) g‖) (polydisc _ r))
    (ih2 : ∀ᵐ u ∂(volume.restrict (polydisc (Fin k × Fin n) r)), eval (normT h T u) g ≠ 0) :
    IntegrableOn (fun u => Real.log ‖eval (normT h (insert i T) u) g‖) (polydisc _ r) ∧
      ∀ᵐ u ∂(volume.restrict (polydisc (Fin k × Fin n) r)), eval (normT h (insert i T) u) g ≠ 0 := by
  have he : ∀ u, eval (normT h (insert i T) u) g =
      (((h.norm fun j => u (i, j) : ℝ) : ℂ)⁻¹) ^ d * eval (normT h T u) g := by
    intro u
    rw [normT_insert h T i hi, eval_scale_of_isWeightedHomogeneous _ _ _ g d hd]
  simp_rw [he]
  have hmeas : Measurable fun u : Fin k × Fin n → ℂ =>
      Real.log ‖(((h.norm fun j => u (i, j) : ℝ) : ℂ)⁻¹) ^ d * eval (normT h T u) g‖ :=
    Real.measurable_log.comp (((Complex.measurable_ofReal.comp (measurable_groupNorm h i)).inv.pow_const
      d).mul ((continuous_eval g).measurable.comp (measurable_normT h T))).norm
  refine ⟨?_, ?_⟩
  · refine Integrable.mono' (g := fun u => d * |Real.log (h.norm fun j => u (i, j))| +
      |Real.log ‖eval (normT h T u) g‖|) ?_ hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => ?_)
    · exact ((integrableOn_log_groupNorm h r i).abs.const_mul _).add ih1.abs
    · rw [Real.norm_eq_abs]
      exact abs_log_inv_pow_mul_le _ (h.li_norm_nonneg _) d _
  ·
    have hnull : ∀ᵐ u ∂(volume.restrict (polydisc (Fin k × Fin n) r)),
        d ≠ 0 → (h.norm fun j => u (i, j)) ≠ 0 := by
      by_cases hd0 : d = 0
      · exact Filter.Eventually.of_forall fun u h' => absurd hd0 h'
      · obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.mpr hg
        have hw := hd (mem_support_iff.mp hm)
        rw [weight_indW] at hw
        obtain ⟨ij, hij, hne⟩ : ∃ ij ∈ m.support, (if inGroup i ij then m ij else 0) ≠ 0 := by
          by_contra hc
          push Not at hc
          rw [Finset.sum_eq_zero hc] at hw
          exact hd0 hw.symm
        have hgi : inGroup i ij := by by_contra hc; simp [hc] at hne
        have hnull0 : volume {u : Fin k × Fin n → ℂ | u ij = 0} = 0 := by
          rw [volume_pi]; exact Measure.pi_hyperplane _ ij 0
        refine ae_restrict_of_ae ?_
        filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull0] with u hu _ h0
        apply hu
        have := congrFun (h.li_eq_zero_of_norm_eq_zero _ h0) ij.2
        simp only [Pi.zero_apply] at this
        have e : (i, ij.2) = ij := by rw [← hgi]
        rw [e] at this
        exact this
    filter_upwards [ih2, hnull] with u hu hn
    refine mul_ne_zero ?_ hu
    by_cases hd0 : d = 0
    · simp [hd0]
    · exact pow_ne_zero _ (inv_ne_zero (Complex.ofReal_ne_zero.mpr (hn hd0)))

theorem logNormT (h : HermNorm n) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ (v : Fin n → ℂ) (j : Fin n), ‖v j‖ ≤ C * h.norm v) (T : Finset (Fin k)) :
    ∀ g : MvPolynomial (Fin k × Fin n) ℂ, g ≠ 0 →
      IntegrableOn (fun u => Real.log ‖eval (normT h T u) g‖) (polydisc _ C) ∧
        ∀ᵐ u ∂(volume.restrict (polydisc (Fin k × Fin n) C)), eval (normT h T u) g ≠ 0 := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro g hg
    have e : normT h (∅ : Finset (Fin k)) = id := by funext u ij; simp [normT]
    simp only [e, id]
    exact ⟨integrableOn_log_norm_eval g hg C, ae_eval_ne_zero g hg C⟩
  | insert i T hi ih =>
    intro g hg
    by_cases hhom : ∃ d, IsWeightedHomogeneous (indW (inGroup i)) g d
    · obtain ⟨d, hd⟩ := hhom
      exact logNormT_insert_of_homog h C T i hi g hg d hd (ih g hg).1 (ih g hg).2
    · obtain ⟨m0, hm0⟩ := MvPolynomial.support_nonempty.mpr hg
      set w := indW (inGroup (n := n) i) with hw
      set d0 := Finsupp.weight w m0 with hd0
      set g' := weightedHomogeneousComponent w d0 g with hg'
      have hg'0 : g' ≠ 0 := by
        intro h0
        have := congrArg (coeff m0) h0
        rw [hg', coeff_weightedHomogeneousComponent, if_pos rfl, coeff_zero] at this
        exact mem_support_iff.mp hm0 this
      obtain ⟨ih1, ih2⟩ := logNormT_insert_of_homog h C T i hi g' hg'0 d0
        (weightedHomogeneousComponent_isWeightedHomogeneous _ _) (ih g' hg'0).1 (ih g' hg'0).2
      obtain ⟨M, hM⟩ := (isCompact_polydisc (ι := Fin k × Fin n) C).exists_bound_of_continuousOn
        (continuous_eval g).continuousOn
      have hD : ∀ m ∈ g.support, Finsupp.weight w m ≤ g.totalDegree :=
        fun m hm => (weight_indW_le _ m).trans (le_totalDegree hm)
      exact circle_lemma volume (polydisc _ C) (measurableSet_polydisc C) (volume_polydisc_ne_top C)
        (fun θ => scaleP (inGroup i) (circleMap 0 1 θ)) (measurable_scaleP _)
        (fun θ => measurePreserving_scaleP _ θ) (fun θ => scale_preimage_polydisc _ θ C)
        (fun u => eval (normT h (insert i T) u) g)
        ((continuous_eval g).measurable.comp (measurable_normT h _))
        (fun d u => eval (normT h (insert i T) u) (weightedHomogeneousComponent w d g))
        g.totalDegree d0 (hD m0 hm0)
        (fun θ u => by
          rw [normT_scaleP]
          exact eval_scaleP _ _ _ g _ hD)
        ih1 ih2 M (fun u hu => hM _ (normT_mem_polydisc h C hC0 hC _ u hu))

end LogInt

end

end GroundTheory.Heights₂.Heights
