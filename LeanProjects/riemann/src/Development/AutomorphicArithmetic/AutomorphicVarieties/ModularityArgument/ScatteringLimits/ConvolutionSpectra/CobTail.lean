import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import GroundTheory.AutomorphicForms.TraceNormComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CutLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.SvSpec

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V]

private theorem expAbs {c : ℝ} (hc : 0 < c) : Integrable fun y : ℝ => Real.exp (-c * |y|) := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  refine IntegrableOn.union ?_ ?_
  · exact (integrableOn_exp_mul_Iic hc 0).congr_fun (fun y hy => by simp only [abs_of_nonpos (mem_Iic.1 hy)]; ring_nf) measurableSet_Iic
  · exact (exp_neg_integrableOn_Ioi 0 hc).congr_fun (fun y hy => by simp only [abs_of_pos (mem_Ioi.1 hy)]) measurableSet_Ioi

private theorem wInt (p : L V) (hp : Tail p) : Integrable fun y => Real.exp (|y| / 2) * ‖p y‖ := by
  obtain ⟨C, hC⟩ := hp
  have ip : Integrable fun x => ‖p x‖ ^ 2 := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable p)).1 (Lp.memLp p)
  have mp : Measurable fun x => ‖p x‖ ^ 2 := (Lp.stronglyMeasurable p).norm.measurable.pow_const 2
  have m2 : Measurable fun x => Real.exp (3 * |x| / 2) * ‖p x‖ ^ 2 :=
    (by fun_prop : Measurable fun x : ℝ => Real.exp (3 * |x| / 2)).mul mp
  have i2 : Integrable fun x => Real.exp (3 * |x| / 2) * ‖p x‖ ^ 2 := by
    refine ⟨m2.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => by positivity)).2 ?_⟩
    have b1 : ∀ᵐ x : ℝ, ENNReal.ofReal (Real.exp (3 * |x| / 2) * ‖p x‖ ^ 2) ≤ ∑' n : ℕ, (Icc (-(n : ℝ)) n)ᶜ.indicator
        (fun x => ENNReal.ofReal (Real.exp (3 * ((n : ℝ) + 1) / 2) * ‖p x‖ ^ 2)) x := by
      filter_upwards [compl_mem_ae_iff.2 (Real.volume_singleton (a := 0))] with x hx
      have h0 : 0 < |x| := abs_pos.2 hx
      have h1 : 1 ≤ ⌈|x|⌉₊ := Nat.one_le_ceil_iff.2 h0
      have h2 : ((⌈|x|⌉₊ - 1 : ℕ) : ℝ) = ⌈|x|⌉₊ - 1 := by rw [Nat.cast_sub h1, Nat.cast_one]
      refine le_trans ?_ (ENNReal.le_tsum (⌈|x|⌉₊ - 1))
      rw [indicator_of_mem (by
        intro h
        have := abs_le.2 h
        linarith [Nat.ceil_lt_add_one h0.le]), h2]
      gcongr
      linarith [Nat.le_ceil |x|]
    refine (lintegral_mono_ae b1).trans_lt ?_
    rw [lintegral_tsum fun n => (Measurable.indicator (by fun_prop) measurableSet_Icc.compl).aemeasurable]
    have b2 : ∀ n : ℕ, ∫⁻ x, (Icc (-(n : ℝ)) n)ᶜ.indicator
        (fun x => ENNReal.ofReal (Real.exp (3 * ((n : ℝ) + 1) / 2) * ‖p x‖ ^ 2)) x ≤
        ENNReal.ofReal (Real.exp (3 / 2) * C ^ 2 * Real.exp (-(1 / 2)) ^ n) := fun n => by
      rw [lintegral_indicator measurableSet_Icc.compl, ← ofReal_integral_eq_lintegral_ofReal (ip.const_mul _).integrableOn
        (Eventually.of_forall fun _ => by positivity), integral_const_mul,
        ← (cutLaws (V := V) _ univ measurableSet_Icc.compl .univ).2.2.2.2.2.2.2.2]
      refine ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hC n (Nat.cast_nonneg n)) 2) (Real.exp_pos _).le).trans_eq ?_)
      rw [mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul, mul_left_comm, ← Real.exp_add, mul_right_comm, ← Real.exp_add, mul_comm]
      congr 2; push_cast; ring
    refine (ENNReal.tsum_le_tsum b2).trans_lt ?_
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity)
      ((summable_geometric_of_lt_one (Real.exp_pos _).le (Real.exp_lt_one_iff.2 (by norm_num))).mul_left _)]
    exact ENNReal.ofReal_lt_top
  refine (i2.add (expAbs (c := 1 / 2) (by norm_num))).mono'
    (((by fun_prop : Continuous fun y : ℝ => Real.exp (|y| / 2)).aestronglyMeasurable).mul (Lp.aestronglyMeasurable _).norm)
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (by positivity), Pi.add_apply]
  have e1 : Real.exp (3 * |y| / 2) = Real.exp (3 * |y| / 4) ^ 2 := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have e2 : Real.exp (-(1 / 2) * |y|) = Real.exp (-|y| / 4) ^ 2 := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have e3 : Real.exp (|y| / 2) = Real.exp (3 * |y| / 4) * Real.exp (-|y| / 4) := by rw [← Real.exp_add]; congr 1; ring
  rw [e1, e2, e3]
  nlinarith [sq_nonneg (Real.exp (3 * |y| / 4) * ‖p y‖ - Real.exp (-|y| / 4)),
    mul_nonneg (mul_pos (Real.exp_pos (3 * |y| / 4)) (Real.exp_pos (-|y| / 4))).le (norm_nonneg (p y))]

private theorem aeInt (q : L V) (hq : Integrable (q : ℝ → V)) (a b : ℝ) :
    ∀ᵐ x : ℝ, (∫ s in Ioc a b, sh V (-s) q : L V) x = ∫ s in Ioc a b, q (x - s) := by
  have hI : Integrable (fun z : ℝ × ℝ => q (z.1 - z.2)) (volume.prod (volume.restrict (Ioc a b))) := by
    simpa using (integrable_const (μ := volume.restrict (Ioc a b)) (1 : ℝ)).convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hq
  have ii : IntegrableOn (fun s => sh V (-s) q) (Ioc a b) :=
    ((shF V).rev.cont q).integrableOn_Ioc
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun A _ hA => integrableOn_Lp_of_measure_ne_top _ (by norm_num) hA.ne) (fun A _ _ => hI.integral_prod_left.integrableOn)
    fun A hm hA => ext_inner_left ℂ fun e => ?_
  have hA' : Integrable (fun z : ℝ × ℝ => q (z.1 - z.2)) ((volume.restrict A).prod (volume.restrict (Ioc a b))) := by
    rw [Measure.restrict_prod_eq_prod_univ]; exact hI.integrableOn
  rw [integral_integral_swap (f := fun x s => q (x - s)) hA', ← integral_inner hA'.integral_prod_right,
    ← L2.inner_indicatorConstLp_eq_inner_setIntegral ℂ hm hA.ne, ← integral_inner ii]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only
  rw [L2.inner_indicatorConstLp_eq_inner_setIntegral]
  congr 1
  exact integral_congr_ae (ae_restrict_of_ae ((sh_ae V (-s) q).mono fun x h => h.trans (congrArg q (sub_eq_add_neg x s).symm)))

private theorem cobOf (q : L V) (wq : Integrable fun y => Real.exp (|y| / 2) * ‖q y‖) (hq : Integrable (q : ℝ → V))
    (h0 : ∫ x, q x = 0) : (shF V).Cob q := by
  set D := ∫ y, Real.exp (|y| / 2) * ‖q y‖
  have hb : ∀ (x : ℝ) (S : Set ℝ), MeasurableSet S → (∀ y ∈ S, |x| ≤ |y|) → ‖∫ y in S, q y‖ ≤ D * Real.exp (-(1 / 2) * |x|) := by
    intro x S hS h
    refine (norm_integral_le_of_norm_le (wq.mul_const (Real.exp (-(1 / 2) * |x|))).integrableOn ?_).trans ?_
    · refine (ae_restrict_iff' hS).2 (Eventually.of_forall fun y hy => ?_)
      rw [mul_right_comm, ← Real.exp_add]
      exact le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp (by linarith [h y hy]))
    · rw [← integral_mul_const]
      exact setIntegral_le_integral (wq.mul_const _) (Eventually.of_forall fun _ => by positivity)
  let k : ℝ → V := fun x => ∫ y in Iic x, q y
  have hk : ∀ x y, k y - k x = ∫ s in x..y, q s := fun x y =>
    intervalIntegral.integral_Iic_sub_Iic hq.integrableOn hq.integrableOn
  have kb : ∀ x, ‖k x‖ ≤ D * Real.exp (-(1 / 2) * |x|) := fun x => by
    rcases le_total x 0 with h | h
    · exact hb x _ measurableSet_Iic fun y hy => by
        rw [abs_of_nonpos h, abs_of_nonpos (le_trans hy h)]; exact neg_le_neg hy
    · have := intervalIntegral.integral_Iic_add_Ioi (b := x) hq.integrableOn hq.integrableOn
      rw [h0] at this
      rw [show k x = -∫ y in Ioi x, q y from eq_neg_of_add_eq_zero_left this, norm_neg]
      exact hb x _ measurableSet_Ioi fun y hy => by
        rw [abs_of_nonneg h]; exact (le_of_lt hy).trans (le_abs_self y)
  have kc : Continuous k := by
    have : k = fun y => k 0 + ∫ s in (0 : ℝ)..y, q s := funext fun y => by rw [← hk]; abel
    rw [this]
    exact continuous_const.add (hq.continuous_primitive 0)
  have km : MemLp k 2 volume := by
    refine (memLp_two_iff_integrable_sq_norm kc.aestronglyMeasurable).2 ?_
    refine ((expAbs one_pos).const_mul (D ^ 2)).mono' (kc.norm.pow 2).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    refine (pow_le_pow_left₀ (norm_nonneg _) (kb x) 2).trans_eq ?_
    rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  refine ⟨km.toLp k, fun t => ?_⟩
  show ∫ s in (0 : ℝ)..t, sh V s q = sh V t (km.toLp k) - km.toLp k
  have e1 : ∫ s in (0 : ℝ)..t, sh V s q = ∫ s in (-t)..0, sh V (-s) q := by
    rw [intervalIntegral.integral_comp_neg fun s => sh V s q]; simp
  rw [e1, intervalIntegral]
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_sub (∫ s in Ioc (-t) 0, sh V (-s) q) (∫ s in Ioc 0 (-t), sh V (-s) q), aeInt q hq (-t) 0, aeInt q hq 0 (-t),
    Lp.coeFn_sub (sh V t (km.toLp k)) (km.toLp k), sh_ae V t (km.toLp k), km.coeFn_toLp,
    (measurePreserving_add_right volume t).quasiMeasurePreserving.ae km.coeFn_toLp] with x h1 h2 h3 h4 h5 h6 h7
  rw [h1, h4, Pi.sub_apply, Pi.sub_apply, h2, h3, h5, h6, h7, hk]
  show ∫ s in (-t)..0, q (x - s) = _
  rw [intervalIntegral.integral_comp_sub_left fun s => q s]; simp
end

theorem UpperTheory.V.Z.IntegralApplyAeEq.cobTail :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (p : L V), (Bdd p → Tail p) ∧ (Tail p → Integrable (p : ℝ → V) ∧ (shF V).Cob (p - one V (∫ x, p x))) := by
  intro V _ _ _ _ p
  have cl := fun s t hs ht => cutLaws (V := V) s t hs ht
  have bt : ∀ p : L V, Bdd p → Tail p := by
    rintro p ⟨ρ₀, h⟩
    refine ⟨Real.exp ρ₀ * ‖p‖, fun ρ hρ => ?_⟩
    by_cases a : ρ₀ ≤ ρ
    · have h2 := DFunLike.congr_fun (cl (Icc (-ρ) ρ)ᶜ (Icc (-ρ₀) ρ₀) measurableSet_Icc.compl measurableSet_Icc).1 p
      rw [ContinuousLinearMap.comp_apply, h, (disjoint_compl_left_iff_subset.2 (Icc_subset_Icc (by linarith) a)).inter_eq,
        (cl univ univ .univ .univ).2.2.2.2.1] at h2
      rw [h2]; simp only [ContinuousLinearMap.zero_apply, norm_zero]; positivity
    · refine ((cl _ univ measurableSet_Icc.compl .univ).2.2.2.2.2.1 _).trans ?_
      rw [mul_right_comm, ← Real.exp_add]
      exact le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp (by linarith [not_le.1 a]))
  refine ⟨bt p, fun hp => ?_⟩
  have wp := wInt p hp
  have toI : ∀ q : L V, Integrable (fun y => Real.exp (|y| / 2) * ‖q y‖) → Integrable (q : ℝ → V) := fun q h =>
    h.mono' (Lp.aestronglyMeasurable q) (Eventually.of_forall fun y =>
      le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp (by positivity)))
  refine ⟨toI p wp, ?_⟩
  obtain ⟨-, o2, o3⟩ := (svSpec (V := V)).2 (∫ x, p x)
  have wo := wInt _ (bt _ o2)
  have hq := Lp.coeFn_sub p (one V (∫ x, p x))
  have h0 : ∫ x, (p - one V (∫ x, p x) : L V) x = 0 := by
    rw [integral_congr_ae hq, integral_sub' (toI p wp) (toI _ wo), o3, sub_self]
  have wq : Integrable fun y => Real.exp (|y| / 2) * ‖(p - one V (∫ x, p x) : L V) y‖ := by
    refine (wp.add wo).mono' (((by fun_prop : Continuous fun y : ℝ => Real.exp (|y| / 2)).aestronglyMeasurable).mul
      (Lp.aestronglyMeasurable _).norm) ?_
    filter_upwards [hq] with y hy
    rw [Real.norm_of_nonneg (by positivity), hy, Pi.add_apply, ← mul_add]
    gcongr
    exact norm_sub_le _ _
  exact cobOf _ wq (toI _ wq) h0
