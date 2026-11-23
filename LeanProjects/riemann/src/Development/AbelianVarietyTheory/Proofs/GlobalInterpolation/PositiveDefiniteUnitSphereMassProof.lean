import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PerpendicularEmbedding
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MeasurePreservingGlue
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFibreFamilyEqAtContinuityPoint

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal

namespace GlobalTheory.SphereMassProof

theorem qf_pos_eq (M : ℕ) (x : Sp M 0) : qf x = ∑ i, ‖x i‖ ^ 2 := by
  simp [qf, Fintype.sum_sum_type, Complex.normSq_eq_norm_sq]

theorem dx_ball (M : ℕ) (hM : 1 ≤ M) (b : ℝ) (hb : 0 ≤ b) :
    dx M 0 {x | qf x ≤ b} = ENNReal.ofReal ((2 * Real.pi) ^ M / (M.factorial : ℝ) * b ^ M) := by
  haveI : Nonempty (Fin M ⊕ Fin 0) := ⟨Sum.inl ⟨0, hM⟩⟩
  have h := Complex.volume_sum_rpow_le (Fin M ⊕ Fin 0) (p := 2) (by norm_num) (Real.sqrt b)
  have e : {x : Sp M 0 | qf x ≤ b} =
      {x : Fin M ⊕ Fin 0 → ℂ | (∑ i, ‖x i‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) ≤ Real.sqrt b} := by
    ext x
    simp only [Set.mem_setOf_eq, ← Real.sqrt_eq_rpow, Real.rpow_two, qf_pos_eq]
    exact (Real.sqrt_le_sqrt_iff hb).symm
  have hc : Fintype.card (Fin M ⊕ Fin 0) = M := by simp
  rw [dx, Measure.smul_apply, e, h, hc, smul_eq_mul]
  have g1 : Real.Gamma (2 / 2 + 1) = 1 := by
    rw [show (2 / 2 + 1 : ℝ) = 2 by norm_num, Real.Gamma_two]
  have g2 : Real.Gamma (2 * (M : ℝ) / 2 + 1) = M.factorial := by
    rw [show (2 * (M : ℝ) / 2 + 1) = M + 1 by ring, Real.Gamma_nat_eq_factorial]
  rw [g1, g2, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), pow_mul, Real.sq_sqrt hb,
    ← ENNReal.ofReal_mul (by positivity), show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
    ← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [mul_pow, add_zero]
  ring

theorem isCompact_shell (M : ℕ) : IsCompact {x : Sp M 0 | qf x ∈ Set.Icc (1 / 2 : ℝ) 2} := by
  refine Metric.isCompact_of_isClosed_isBounded
    (isClosed_Icc.preimage GlobalTheory.RealPlaceCompare.continuous_qf) ?_
  refine (Metric.isBounded_closedBall (x := (0 : Sp M 0)) (r := 2)).subset fun x hx => ?_
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by norm_num)]
  intro i
  have h1 : ‖x i‖ ^ 2 ≤ ∑ j, ‖x j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖x j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have h2 : qf x ≤ 2 := hx.2
  rw [qf_pos_eq] at h2
  nlinarith [norm_nonneg (x i)]

theorem exists_mass {M : ℕ} {fib : ℝ → Measure (Sp M 0)} (h : IsDxDq fib) :
    ∃ G : ℝ → ℝ, Continuous G ∧ (∀ t, 0 ≤ G t) ∧
      ∀ t ∈ Set.Icc (1 / 2 : ℝ) 2, fib t Set.univ = ENNReal.ofReal (G t) := by
  obtain ⟨χ, h1, hc, hs, h01⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen
    (isCompact_shell M) (isOpen_ne (x := (0 : Sp M 0))) (by
      rintro x hx rfl
      have : (1 / 2 : ℝ) ≤ qf (0 : Sp M 0) := hx.1
      rw [qf_pos_eq] at this
      norm_num at this)
  obtain ⟨hi, hg⟩ := h.2.2 χ χ.continuous hc hs
  refine ⟨fun t => ∫ v, χ v ∂(fib t), continuousOn_univ.1 hg,
    fun t => integral_nonneg fun v => (h01 v).1, fun t ht => ?_⟩
  rw [ofReal_integral_eq_lintegral_ofReal (hi t trivial)
    (Filter.Eventually.of_forall fun v => (h01 v).1), ← lintegral_one]
  apply lintegral_congr_ae
  filter_upwards [GlobalTheory.RealPlaceCompare.ae_qf h t] with v hv
  have : χ v = 1 := h1 (show qf v ∈ Set.Icc (1 / 2 : ℝ) 2 from hv ▸ ht)
  simp [this]

theorem dx_shell {M : ℕ} {fib : ℝ → Measure (Sp M 0)} (h : IsDxDq fib) (a b : ℝ) (ha : 0 ≤ a) :
    dx M 0 (qf ⁻¹' Set.Ioc a b) = ∫⁻ t in Set.Ioc a b, fib t Set.univ := by
  have hq : Measurable (qf : Sp M 0 → ℝ) := GlobalTheory.RealPlaceCompare.continuous_qf.measurable
  have hO : MeasurableSet {x : Sp M 0 | x ≠ 0} := isOpen_ne.measurableSet
  have key := GlobalTheory.IsFibreFamily_lintegral_preimage hq isOpen_ne subset_rfl h
    (({x : Sp M 0 | x ≠ 0}).indicator 1) (measurable_one.indicator hO)
    (fun v hv => Set.indicator_of_notMem hv _) (Set.Ioc a b) measurableSet_Ioc
  have hsub : qf ⁻¹' Set.Ioc a b ⊆ {x : Sp M 0 | x ≠ 0} := by
    rintro x hx rfl
    have : a < qf (0 : Sp M 0) := hx.1
    rw [qf_pos_eq] at this
    norm_num at this
    linarith
  rw [Set.indicator_indicator, Set.inter_eq_left.2 hsub,
    lintegral_indicator_one (hq measurableSet_Ioc), Measure.restrict_apply (hq measurableSet_Ioc),
    Set.inter_eq_left.2 hsub] at key
  rw [key]
  refine lintegral_congr fun t => ?_
  rw [lintegral_indicator_one hO]
  refine measure_congr (Filter.eventuallyEq_univ.2 ?_)
  have h1 : ∀ᵐ y ∂(fib t), y ∈ qf ⁻¹' {id t} ∩ {x : Sp M 0 | x ≠ 0} := h.1 t
  filter_upwards [h1] with y hy using hy.2

theorem sphereMass : SphereMass := by
  intro M hM
  refine ⟨GlobalTheory.RealPlaceCompare.exists_isDxDq M 0, fun fib h => ?_⟩
  obtain ⟨G, hG, hG0, hGm⟩ := exists_mass h
  have hq : Measurable (qf : Sp M 0 → ℝ) := GlobalTheory.RealPlaceCompare.continuous_qf.measurable
  set C : ℝ := (2 * Real.pi) ^ M / (M.factorial : ℝ) with hC
  have hC0 : 0 ≤ C := by have := Real.pi_pos; positivity
  have hint : ∀ b ∈ Set.Ioo (1 / 2 : ℝ) 2,
      ∫ t in (1 / 2 : ℝ)..b, G t = C * b ^ M - C * (1 / 2) ^ M := by
    intro b hb
    have hb0 : 0 ≤ b := by linarith [hb.1]
    have e1 : qf ⁻¹' Set.Ioc (1 / 2 : ℝ) b =
        {x : Sp M 0 | qf x ≤ b} \ {x | qf x ≤ 1 / 2} := by
      ext x; simp [and_comm]
    have e2 := dx_shell h (1 / 2) b (by norm_num)
    have hfin : dx M 0 {x : Sp M 0 | qf x ≤ 1 / 2} ≠ ⊤ := by
      rw [dx_ball M hM _ (by norm_num)]; exact ENNReal.ofReal_ne_top
    rw [e1, measure_diff (s₁ := {x : Sp M 0 | qf x ≤ b}) (s₂ := {x : Sp M 0 | qf x ≤ 1 / 2})
      (fun x (hx : qf x ≤ 1 / 2) => (hx.trans hb.1.le : qf x ≤ b))
      (measurableSet_le hq measurable_const).nullMeasurableSet hfin,
      dx_ball M hM _ hb0, dx_ball M hM _ (by norm_num), ← hC,
      ← ENNReal.ofReal_sub _ (by positivity),
      setLIntegral_congr_fun measurableSet_Ioc
        (fun t ht => hGm t ⟨ht.1.le, ht.2.trans hb.2.le⟩),
      ← ofReal_integral_eq_lintegral_ofReal (hG.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
        (Filter.Eventually.of_forall hG0)] at e2
    rw [intervalIntegral.integral_of_le hb.1.le]
    refine ((ENNReal.ofReal_eq_ofReal_iff ?_ (integral_nonneg hG0)).1 e2).symm
    have : (1 / 2 : ℝ) ^ M ≤ b ^ M := pow_le_pow_left₀ (by norm_num) hb.1.le M
    nlinarith
  have d1 : HasDerivAt (fun b => ∫ t in (1 / 2 : ℝ)..b, G t) (G 1) 1 :=
    (hG.integral_hasStrictDerivAt _ _).hasDerivAt
  have d2 : HasDerivAt (fun b : ℝ => C * b ^ M - C * (1 / 2) ^ M)
      (C * ((M : ℝ) * 1 ^ (M - 1))) 1 := ((hasDerivAt_pow M 1).const_mul C).sub_const _
  have d3 : HasDerivAt (fun b => ∫ t in (1 / 2 : ℝ)..b, G t) (C * ((M : ℝ) * 1 ^ (M - 1))) 1 := by
    refine d2.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num) (show (1 : ℝ) < 2 by norm_num)]
      with b hb using hint b hb
  rw [hGm 1 ⟨by norm_num, by norm_num⟩, d1.unique d3, hC, cM]
  congr 1
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
  have hk : ((k.factorial : ℝ)) ≠ 0 := by positivity
  have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  simp only [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    one_pow, mul_one]
  field_simp

end GlobalTheory.SphereMassProof
