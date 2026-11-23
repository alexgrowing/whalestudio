import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.SdUniq

noncomputable section

namespace PI.OmFibreUniq.W.SdCore

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Topology Filter
open PI.VolStabSW.SdUniqW
open scoped ENNReal

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
  [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]

theorem chi_zero_left (χ : V → V → ℂ) (hχ : ∀ x t y, χ (t + x) y = χ t y * χ x y)
    (hn : ∀ x y, ‖χ x y‖ = 1) (y : V) : χ 0 y = 1 := by
  have h := hχ 0 0 y
  rw [add_zero] at h
  have hne : χ 0 y ≠ 0 := by
    intro h0
    have := hn 0 y
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  have h2 : χ 0 y * (χ 0 y - 1) = 0 := by rw [mul_sub, ← h, mul_one, sub_self]
  rcases mul_eq_zero.1 h2 with h1 | h1
  · exact absurd h1 hne
  · exact sub_eq_zero.1 h1

theorem zero_mem_ann (χ : V → V → ℂ) (hχ : ∀ x t y, χ (t + x) y = χ t y * χ x y)
    (hsym : ∀ x y, χ x y = χ y x) (hn : ∀ x y, ‖χ x y‖ = 1) (L : Set V) : (0 : V) ∈ ann χ L := by
  intro x _
  rw [hsym]
  exact chi_zero_left χ hχ hn x

theorem exists_normalized (μ0 : Measure V) [μ0.IsAddHaarMeasure] (A B : ℕ → Set V)
    (hAc : ∀ k, IsCompact (A k)) (hBc : ∀ k, IsCompact (B k)) (hAo : IsOpen (A 0))
    (hBo : IsOpen (B 0)) (hA0 : (A 0).Nonempty) (hB0 : (B 0).Nonempty)
    (hconst : ∀ k, μ0 (A k) * μ0 (B k) = μ0 (A 0) * μ0 (B 0)) :
    ∃ μ : Measure V, μ.IsAddHaarMeasure ∧ ∀ k, μ.real (A k) * μ.real (B k) = 1 := by
  have ha0 : μ0 (A 0) ≠ 0 := (hAo.measure_pos μ0 hA0).ne'
  have hb0 : μ0 (B 0) ≠ 0 := (hBo.measure_pos μ0 hB0).ne'
  have hat : μ0 (A 0) ≠ ⊤ := (hAc 0).measure_lt_top.ne
  have hbt : μ0 (B 0) ≠ ⊤ := (hBc 0).measure_lt_top.ne
  set c : ℝ := (μ0 (A 0) * μ0 (B 0)).toReal with hc
  have hcpos : 0 < c := ENNReal.toReal_pos (mul_ne_zero ha0 hb0) (ENNReal.mul_ne_top hat hbt)
  set s : ℝ := Real.sqrt c with hs
  have hspos : 0 < s := Real.sqrt_pos.2 hcpos
  have hss : s * s = c := Real.mul_self_sqrt hcpos.le
  set r : ℝ≥0∞ := ENNReal.ofReal (1 / s) with hr
  have hr0 : r ≠ 0 := by
    rw [hr, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hrt : r ≠ ⊤ := ENNReal.ofReal_ne_top
  refine ⟨r • μ0, Measure.IsAddHaarMeasure.smul (μ := μ0) hr0 hrt, fun k => ?_⟩
  have hk : (μ0 (A k)).toReal * (μ0 (B k)).toReal = c := by
    rw [← ENNReal.toReal_mul, hconst k]
  simp only [Measure.real, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul]
  rw [hr, ENNReal.toReal_ofReal (by positivity)]
  calc 1 / s * (μ0 (A k)).toReal * (1 / s * (μ0 (B k)).toReal)
      = ((μ0 (A k)).toReal * (μ0 (B k)).toReal) / (s * s) := by field_simp
    _ = 1 := by rw [hk, hss, div_self hcpos.ne']

section Inv

variable (χ : V → V → ℂ) (hχc : Continuous (fun p : V × V => χ p.1 p.2))
  (hχ : ∀ x t y, χ (t + x) y = χ t y * χ x y) (hsym : ∀ x y, χ x y = χ y x)
  (hn : ∀ x y, ‖χ x y‖ = 1)
  (μ : Measure V) [μ.IsAddHaarMeasure] (M : AddSubgroup V) (hMc : IsCompact (M : Set V))
  (hMo : IsOpen (M : Set V))

include hχc in
theorem isClosed_ann : IsClosed (ann χ (M : Set V)) := by
  have : ann χ (M : Set V) = ⋂ x ∈ (M : Set V), {y | χ x y = 1} := by
    ext y; simp [ann]
  rw [this]
  exact isClosed_biInter fun x _ =>
    isClosed_eq (hχc.comp (continuous_const.prodMk continuous_id)) continuous_const

include hχc hχ hsym hn hMc hMo in

theorem key (Φ : V → ℂ) (hc : Continuous Φ) (hs : HasCompactSupport Φ) (z : V) :
    ∫ y in (M : Set V), (∫ x, Φ x * χ x y ∂μ) * χ y z ∂μ =
      (μ.real (M : Set V) : ℂ) * ∫ u in ann χ M, Φ (u - z) ∂μ := by
  have hΦi : Integrable Φ μ := hc.integrable_of_hasCompactSupport hs
  have hm : MeasurableSet (M : Set V) := hMo.measurableSet
  have h1 : ∀ y, (∫ x, Φ x * χ x y ∂μ) * χ y z = ∫ x, Φ x * χ (x + z) y ∂μ := by
    intro y
    rw [← integral_mul_const]
    congr 1
    funext x
    rw [hχ z x y, hsym z y, mul_assoc]
  simp only [h1]
  haveI : IsFiniteMeasure (μ.restrict (M : Set V)) :=
    isFiniteMeasure_restrict.2 hMc.measure_lt_top.ne
  have hint : Integrable (Function.uncurry fun (y x : V) => Φ x * χ (x + z) y)
      ((μ.restrict (M : Set V)).prod μ) := by
    have hb : Integrable (fun p : V × V => (1 : ℝ) * ‖Φ p.2‖) ((μ.restrict (M : Set V)).prod μ) :=
      Integrable.mul_prod (integrable_const (1 : ℝ)) hΦi.norm
    refine hb.mono' ?_ ?_
    · have hcont : Continuous (Function.uncurry fun (y x : V) => Φ x * χ (x + z) y) := by
        show Continuous fun p : V × V => Φ p.2 * χ (p.2 + z) p.1
        exact (hc.comp continuous_snd).mul
          (hχc.comp ((continuous_snd.add continuous_const).prodMk continuous_fst))
      exact hcont.aestronglyMeasurable
    · filter_upwards with p
      simp [Function.uncurry, norm_mul, hn]
  rw [integral_integral_swap hint]
  have h2 : ∀ x, ∫ y in (M : Set V), Φ x * χ (x + z) y ∂μ =
      (ann χ M).indicator (fun _ => (μ.real (M : Set V) : ℂ)) (x + z) * Φ x := by
    intro x
    rw [integral_const_mul, ← transform_indicator μ χ hχ M hMo (x + z), ← integral_indicator hm,
      mul_comm]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    by_cases hy : y ∈ (M : Set V)
    · simp [Set.indicator_of_mem hy, hsym]
    · simp [Set.indicator_of_notMem hy]
  simp only [h2]
  have h3 : ∀ x, (ann χ M).indicator (fun _ => (μ.real (M : Set V) : ℂ)) (x + z) * Φ x =
      (μ.real (M : Set V) : ℂ) * (ann χ M).indicator (fun u => Φ (u - z)) (x + z) := by
    intro x
    by_cases hx : x + z ∈ ann χ M
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  simp only [h3]
  rw [integral_const_mul,
    integral_add_right_eq_self (fun w => (ann χ M).indicator (fun u => Φ (u - z)) w) z,
    integral_indicator (isClosed_ann χ hχc M).measurableSet]

end Inv

theorem selfDual_of_pairs (χ : V → V → ℂ) (hχc : Continuous (fun p : V × V => χ p.1 p.2))
    (hχ : ∀ x t y, χ (t + x) y = χ t y * χ x y) (hsym : ∀ x y, χ x y = χ y x)
    (hn : ∀ x y, ‖χ x y‖ = 1)
    (M : ℕ → AddSubgroup V) (hMc : ∀ k, IsCompact (M k : Set V)) (hMo : ∀ k, IsOpen (M k : Set V))
    (hNc : ∀ k, IsCompact (ann χ (M k))) (hNo : ∀ k, IsOpen (ann χ (M k)))
    (hex : ∀ y, ∀ᶠ k in atTop, y ∈ M k)
    (hsh : ∀ U ∈ 𝓝 (0 : V), ∀ᶠ k in atTop, ann χ (M k) ⊆ U)
    (μ0 : Measure V) [μ0.IsAddHaarMeasure]
    (hconst : ∀ k, μ0 (M k) * μ0 (ann χ (M k)) = μ0 (M 0) * μ0 (ann χ (M 0))) :
    ∃ μ : Measure V, SelfDual μ χ := by
  obtain ⟨μ, hμ, hprod⟩ := exists_normalized μ0 (fun k => (M k : Set V)) (fun k => ann χ (M k))
    hMc hNc (hMo 0) (hNo 0) ⟨0, (M 0).zero_mem⟩ ⟨0, zero_mem_ann χ hχ hsym hn _⟩ hconst
  refine ⟨μ, hμ, fun Φ hc hs hI z => ?_⟩
  set I : V → ℂ := fun y => ∫ x, Φ x * χ x y ∂μ with hIdef
  have hL : Tendsto (fun k => ∫ y, (M k : Set V).indicator (fun y => I y * χ y z) y ∂μ) atTop
      (𝓝 (∫ y, I y * χ y z ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun y => ‖I y‖) (fun k => ?_) hI.norm
      (fun k => ?_) ?_
    · exact (hI.aestronglyMeasurable.mul
        (hχc.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable).indicator
        (hMo k).measurableSet
    · filter_upwards with y
      by_cases hy : y ∈ (M k : Set V)
      · simp [Set.indicator_of_mem hy, norm_mul, hn]
      · simp [Set.indicator_of_notMem hy]
    · filter_upwards with y
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hex y] with k hk
      simp [Set.indicator_of_mem (SetLike.mem_coe.2 hk)]
  have hR : Tendsto (fun k => (μ.real (M k : Set V) : ℂ) * ∫ u in ann χ (M k), Φ (u - z) ∂μ) atTop
      (𝓝 (Φ (-z))) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hcz : Continuous (fun u => Φ (u - z)) := hc.comp (continuous_id.sub continuous_const)
    have hU : {u : V | dist (Φ (u - z)) (Φ (-z)) < ε / 2} ∈ 𝓝 (0 : V) := by
      have h0 : Φ ((0 : V) - z) = Φ (-z) := by rw [zero_sub]
      exact hcz.continuousAt.preimage_mem_nhds (by rw [h0]; exact Metric.ball_mem_nhds _ (half_pos hε))
    filter_upwards [hsh _ hU] with k hk
    have hmn := hprod k
    have hfin : μ (ann χ (M k)) < ⊤ := (hNc k).measure_lt_top
    have hio : IntegrableOn (fun u => Φ (u - z)) (ann χ (M k)) μ := hcz.continuousOn.integrableOn_compact (hNc k)
    have e : (μ.real (M k : Set V) : ℂ) * ∫ u in ann χ (M k), Φ (u - z) ∂μ - Φ (-z) =
        (μ.real (M k : Set V) : ℂ) * ∫ u in ann χ (M k), (Φ (u - z) - Φ (-z)) ∂μ := by
      rw [integral_sub hio (integrableOn_const hfin.ne), setIntegral_const, mul_sub]
      congr 1
      rw [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, hmn, Complex.ofReal_one, one_mul]
    rw [dist_eq_norm, e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    have hb : ‖∫ u in ann χ (M k), (Φ (u - z) - Φ (-z)) ∂μ‖ ≤ ε / 2 * μ.real (ann χ (M k)) := by
      refine norm_setIntegral_le_of_norm_le_const hfin fun u hu => ?_
      have := hk hu
      simp only [Set.mem_setOf_eq, dist_eq_norm] at this
      exact this.le
    calc μ.real (M k : Set V) * ‖∫ u in ann χ (M k), (Φ (u - z) - Φ (-z)) ∂μ‖
        ≤ μ.real (M k : Set V) * (ε / 2 * μ.real (ann χ (M k))) :=
          mul_le_mul_of_nonneg_left hb measureReal_nonneg
      _ = ε / 2 := by rw [mul_comm (ε / 2), ← mul_assoc, hmn, one_mul]
      _ < ε := half_lt_self hε
  have hEq : (fun k => ∫ y, (M k : Set V).indicator (fun y => I y * χ y z) y ∂μ) =
      fun k => (μ.real (M k : Set V) : ℂ) * ∫ u in ann χ (M k), Φ (u - z) ∂μ := by
    funext k
    rw [integral_indicator (hMo k).measurableSet]
    exact key χ hχc hχ hsym hn μ (M k) (hMc k) (hMo k) Φ hc hs z
  rw [hEq] at hL
  exact tendsto_nhds_unique hL hR

end PI.OmFibreUniq.W.SdCore
