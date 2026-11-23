import Formalism.HermitianCurvature.HermitianCurvatureProofs.RootPushforwardDensity
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ContinuousMapDense

namespace Formalism.FourierDecayAlt.P.PBK

open MeasureTheory Filter Topology
open scoped InnerProductSpace

noncomputable section

section dil

theorem map_mul_volume (ρ : ℂ) (hρ : ρ ≠ 0) :
    Measure.map (fun z : ℂ => ρ * z) volume = ENNReal.ofReal ((‖ρ‖ ^ 2)⁻¹) • (volume : Measure ℂ) := by
  have hdet : LinearMap.det (LinearMap.mulLeft ℝ ρ) = ‖ρ‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Algebra.norm_complex_apply, Algebra.norm_apply]
    rfl
  have hne : LinearMap.det (LinearMap.mulLeft ℝ ρ) ≠ 0 := by
    rw [hdet]
    positivity
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure ℂ) hne
  rw [hdet, abs_of_nonneg (by positivity)] at h
  exact h

def mulEquiv (ρ : ℂ) (hρ : ρ ≠ 0) : ℂ ≃ᵐ ℂ := (Homeomorph.mulLeft₀ ρ hρ).toMeasurableEquiv

theorem mulEquiv_apply (ρ : ℂ) (hρ : ρ ≠ 0) (z : ℂ) : mulEquiv ρ hρ z = ρ * z := rfl

theorem map_mulEquiv (ρ : ℂ) (hρ : ρ ≠ 0) :
    Measure.map (mulEquiv ρ hρ) volume = ENNReal.ofReal ((‖ρ‖ ^ 2)⁻¹) • (volume : Measure ℂ) := by
  have h : ⇑(mulEquiv ρ hρ) = fun z => ρ * z := funext (mulEquiv_apply ρ hρ)
  rw [h]
  exact map_mul_volume ρ hρ

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem integral_comp_mul_C (g : ℂ → E) (ρ : ℂ) (hρ : ρ ≠ 0) :
    ∫ z, g (ρ * z) = (‖ρ‖ ^ 2)⁻¹ • ∫ z, g z := by
  have h := integral_map_equiv (μ := (volume : Measure ℂ)) (mulEquiv ρ hρ) g
  rw [map_mulEquiv, integral_smul_measure, ENNReal.toReal_ofReal (by positivity)] at h
  exact h.symm

theorem memLp_comp_mul {p : ENNReal} {f : ℂ → E} (hf : MemLp f p volume) (ρ : ℂ) (hρ : ρ ≠ 0) :
    MemLp (fun z => f (ρ * z)) p volume := by
  have h1 : MemLp f p (Measure.map (mulEquiv ρ hρ) volume) := by
    rw [map_mulEquiv]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  exact h1.comp_of_map (mulEquiv ρ hρ).measurable.aemeasurable

theorem integral_norm_dil_sq (f : ℂ → E) (ρ : ℂ) (hρ : ρ ≠ 0) :
    ∫ z, ‖‖ρ‖ • f (ρ * z)‖ ^ 2 = ∫ z, ‖f z‖ ^ 2 := by
  have hρ0 : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ
  have e : (fun z => ‖‖ρ‖ • f (ρ * z)‖ ^ 2) = fun z => ‖ρ‖ ^ 2 * ‖f (ρ * z)‖ ^ 2 := by
    funext z
    rw [norm_smul, norm_norm, mul_pow]
  rw [e, integral_const_mul, integral_comp_mul_C (fun z => ‖f z‖ ^ 2) ρ hρ, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ (by positivity), one_mul]

theorem memLp_dil {f : ℂ → E} (hf : MemLp f 2 volume) (ρ : ℂ) (hρ : ρ ≠ 0) :
    MemLp (fun z => ‖ρ‖ • f (ρ * z)) 2 volume :=
  (memLp_comp_mul hf ρ hρ).const_smul ‖ρ‖

theorem integrable_sq_of_memLp {u : ℂ → E} (hu : MemLp u 2 volume) : Integrable (fun z => ‖u z‖ ^ 2) volume :=
  (memLp_two_iff_integrable_sq_norm hu.1).1 hu

theorem tendsto_dil_cpt (g : ℂ → E) (hgc : Continuous g) (hgs : HasCompactSupport g) (ζ : ℂ) (hζ : ζ ≠ 0) :
    Tendsto (fun ρ : ℂ => ∫ z, ‖‖ρ‖ • g (ρ * z) - ‖ζ‖ • g (ζ * z)‖ ^ 2) (𝓝 ζ) (𝓝 0) := by
  obtain ⟨M, hM⟩ := hgc.bounded_above_of_compact_support hgs
  obtain ⟨R, hR⟩ := hgs.isCompact.isBounded.subset_closedBall (0 : ℂ)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hζ0 : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ
  have hzero : ∀ w : ℂ, max R 0 < ‖w‖ → g w = 0 := by
    intro w hw
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have h1 := hR hmem
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    linarith [le_max_left R 0]
  have hR0 : 0 ≤ max R 0 := le_max_right R 0
  have hr0 : 0 ≤ 2 * max R 0 / ‖ζ‖ := by positivity
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (F := fun ρ z => ‖‖ρ‖ • g (ρ * z) - ‖ζ‖ • g (ζ * z)‖ ^ 2)
    (f := fun z => ‖‖ζ‖ • g (ζ * z) - ‖ζ‖ • g (ζ * z)‖ ^ 2)
    (μ := volume) (l := 𝓝 ζ)
    ((Metric.closedBall (0 : ℂ) (2 * max R 0 / ‖ζ‖)).indicator fun _ => (3 * ‖ζ‖ * M) ^ 2) ?_ ?_ ?_ ?_
  · simpa using hlim
  · refine Filter.Eventually.of_forall fun ρ => ?_
    have hc : Continuous fun z => ‖‖ρ‖ • g (ρ * z) - ‖ζ‖ • g (ζ * z)‖ ^ 2 := by fun_prop
    exact hc.aestronglyMeasurable
  · have hball : Metric.ball ζ (‖ζ‖ / 2) ∈ 𝓝 ζ := Metric.ball_mem_nhds ζ (by positivity)
    filter_upwards [hball] with ρ hρ
    refine Filter.Eventually.of_forall fun z => ?_
    rw [Metric.mem_ball, dist_eq_norm] at hρ
    have hρlo : ‖ζ‖ / 2 ≤ ‖ρ‖ := by
      have h1 := norm_sub_norm_le ζ ρ
      rw [norm_sub_rev] at h1
      linarith
    have hρhi : ‖ρ‖ ≤ 2 * ‖ζ‖ := by
      have h1 := norm_le_insert' ρ ζ
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    by_cases hz : z ∈ Metric.closedBall (0 : ℂ) (2 * max R 0 / ‖ζ‖)
    · rw [Set.indicator_of_mem hz]
      have h1 : ‖‖ρ‖ • g (ρ * z) - ‖ζ‖ • g (ζ * z)‖ ≤ 3 * ‖ζ‖ * M := by
        calc ‖‖ρ‖ • g (ρ * z) - ‖ζ‖ • g (ζ * z)‖
            ≤ ‖‖ρ‖ • g (ρ * z)‖ + ‖‖ζ‖ • g (ζ * z)‖ := norm_sub_le _ _
          _ = ‖ρ‖ * ‖g (ρ * z)‖ + ‖ζ‖ * ‖g (ζ * z)‖ := by
              rw [norm_smul, norm_smul, norm_norm, norm_norm]
          _ ≤ 2 * ‖ζ‖ * M + ‖ζ‖ * M :=
              add_le_add (mul_le_mul hρhi (hM _) (norm_nonneg _) (by positivity))
                (mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _))
          _ = 3 * ‖ζ‖ * M := by ring
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    · rw [Set.indicator_of_notMem hz]
      rw [Metric.mem_closedBall, dist_zero_right, not_le] at hz
      have e1 : g (ρ * z) = 0 := by
        apply hzero
        rw [norm_mul]
        calc max R 0 = ‖ζ‖ / 2 * (2 * max R 0 / ‖ζ‖) := by field_simp
          _ < ‖ζ‖ / 2 * ‖z‖ := by gcongr
          _ ≤ ‖ρ‖ * ‖z‖ := by gcongr
      have e2 : g (ζ * z) = 0 := by
        apply hzero
        rw [norm_mul]
        calc max R 0 ≤ ‖ζ‖ / 2 * (2 * max R 0 / ‖ζ‖) := by field_simp; rfl
          _ < ‖ζ‖ / 2 * ‖z‖ := by gcongr
          _ ≤ ‖ζ‖ * ‖z‖ := by gcongr; linarith
      rw [e1, e2]
      simp
  · exact (integrableOn_const measure_closedBall_lt_top.ne).integrable_indicator
      Metric.isClosed_closedBall.measurableSet
  · refine Filter.Eventually.of_forall fun z => ?_
    have hc : Continuous fun ρ : ℂ => ‖‖ρ‖ • g (ρ * z) - ‖ζ‖ • g (ζ * z)‖ ^ 2 := by fun_prop
    exact hc.tendsto ζ

theorem tendsto_dil (f : ℂ → E) (hf : MemLp f 2 volume) (ζ : ℂ) (hζ : ζ ≠ 0) :
    Tendsto (fun ρ : ℂ => ∫ z, ‖‖ρ‖ • f (ρ * z) - ‖ζ‖ • f (ζ * z)‖ ^ 2) (𝓝 ζ) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hf' : MemLp f (ENNReal.ofReal 2) volume := by simpa using hf
  obtain ⟨g, hgs, hfg, hgc, hgm⟩ :=
    hf'.exists_hasCompactSupport_integral_rpow_sub_le two_pos (ε := ε / 12) (by positivity)
  have hfg' : ∫ z, ‖f z - g z‖ ^ 2 ≤ ε / 12 := by
    have e : (fun z => ‖f z - g z‖ ^ (2 : ℝ)) = fun z => ‖f z - g z‖ ^ 2 := by
      funext z
      exact Real.rpow_two _
    rw [e] at hfg
    exact hfg
  have hgm2 : MemLp g 2 volume := by simpa using hgm
  have hT := tendsto_dil_cpt g hgc hgs ζ hζ
  rw [Metric.tendsto_nhds] at hT
  filter_upwards [hT (ε / 6) (by positivity), eventually_ne_nhds hζ] with ρ hρT hρ0
  have hnn : ∀ (h : ℂ → ℝ), 0 ≤ ∫ z, ‖h z‖ ^ 2 := fun h => integral_nonneg fun _ => by positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => by positivity)] at hρT ⊢
  have h3 : ∀ a b c : E, ‖a + b + c‖ ^ 2 ≤ 3 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) := by
    intro a b c
    have h1 := norm_add₃_le (a := a) (b := b) (c := c)
    have h2 : ‖a + b + c‖ ^ 2 ≤ (‖a‖ + ‖b‖ + ‖c‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖b‖ - ‖c‖), sq_nonneg (‖a‖ - ‖c‖)]
  have hdfg : MemLp (fun z => f z - g z) 2 volume := hf.sub hgm2
  have hdgf : MemLp (fun z => g z - f z) 2 volume := hgm2.sub hf
  have iA := integrable_sq_of_memLp (memLp_dil hdfg ρ hρ0)
  have iB := integrable_sq_of_memLp ((memLp_dil hgm2 ρ hρ0).sub (memLp_dil hgm2 ζ hζ))
  have iC := integrable_sq_of_memLp (memLp_dil hdgf ζ hζ)
  have iL := integrable_sq_of_memLp ((memLp_dil hf ρ hρ0).sub (memLp_dil hf ζ hζ))
  have hA := integral_norm_dil_sq (fun w => f w - g w) ρ hρ0
  have hC := integral_norm_dil_sq (fun w => g w - f w) ζ hζ
  have hgf : ∫ z, ‖g z - f z‖ ^ 2 = ∫ z, ‖f z - g z‖ ^ 2 := by
    congr 1
    funext z
    rw [norm_sub_rev]
  have hmono : ∫ z, ‖‖ρ‖ • f (ρ * z) - ‖ζ‖ • f (ζ * z)‖ ^ 2 ≤
      ∫ z, 3 * (‖‖ρ‖ • (f (ρ * z) - g (ρ * z))‖ ^ 2 +
        ‖‖ρ‖ • g (ρ * z) - ‖ζ‖ • g (ζ * z)‖ ^ 2 + ‖‖ζ‖ • (g (ζ * z) - f (ζ * z))‖ ^ 2) := by
    refine integral_mono iL (((iA.add iB).add iC).const_mul 3) fun z => ?_
    have e : ‖ρ‖ • f (ρ * z) - ‖ζ‖ • f (ζ * z) = ‖ρ‖ • (f (ρ * z) - g (ρ * z)) +
        (‖ρ‖ • g (ρ * z) - ‖ζ‖ • g (ζ * z)) + ‖ζ‖ • (g (ζ * z) - f (ζ * z)) := by
      rw [smul_sub, smul_sub]
      abel
    simp only
    rw [e]
    exact h3 _ _ _
  have hs1 : ∫ z, (‖‖ρ‖ • (f (ρ * z) - g (ρ * z))‖ ^ 2 +
        ‖‖ρ‖ • g (ρ * z) - ‖ζ‖ • g (ζ * z)‖ ^ 2 + ‖‖ζ‖ • (g (ζ * z) - f (ζ * z))‖ ^ 2) =
      (∫ z, (‖‖ρ‖ • (f (ρ * z) - g (ρ * z))‖ ^ 2 + ‖‖ρ‖ • g (ρ * z) - ‖ζ‖ • g (ζ * z)‖ ^ 2)) +
        ∫ z, ‖‖ζ‖ • (g (ζ * z) - f (ζ * z))‖ ^ 2 :=
    integral_add (iA.add iB) iC
  have hs2 : ∫ z, (‖‖ρ‖ • (f (ρ * z) - g (ρ * z))‖ ^ 2 + ‖‖ρ‖ • g (ρ * z) - ‖ζ‖ • g (ζ * z)‖ ^ 2) =
      (∫ z, ‖‖ρ‖ • (f (ρ * z) - g (ρ * z))‖ ^ 2) + ∫ z, ‖‖ρ‖ • g (ρ * z) - ‖ζ‖ • g (ζ * z)‖ ^ 2 :=
    integral_add iA iB
  rw [integral_const_mul, hs1, hs2] at hmono
  rw [hA, hC, hgf] at hmono
  linarith

theorem tendsto_inner_dil {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (b c : ℂ → H)
    (hb : MemLp b 2 volume) (hc : MemLp c 2 volume) (ζ : ℂ) (hζ : ζ ≠ 0) :
    Tendsto (fun ρ : ℂ => ∫ z, ‖⟪b z, ((‖ρ‖ : ℝ) : ℂ) • c (ρ * z)⟫_ℂ - ⟪b z, ((‖ζ‖ : ℝ) : ℂ) • c (ζ * z)⟫_ℂ‖)
      (𝓝 ζ) (𝓝 0) := by
  have hT := tendsto_dil c hc ζ hζ
  set K : ℝ := (∫ z, ‖b z‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ))
  have hG : Tendsto (fun ρ : ℂ => K * (∫ z, ‖‖ρ‖ • c (ρ * z) - ‖ζ‖ • c (ζ * z)‖ ^ 2) ^ (1 / (2 : ℝ)))
      (𝓝 ζ) (𝓝 0) := by
    have h1 := ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 2)).tendsto 0).comp hT
    rw [Real.zero_rpow (by norm_num)] at h1
    simpa using h1.const_mul K
  refine squeeze_zero' (Filter.Eventually.of_forall fun ρ => integral_nonneg fun _ => norm_nonneg _) ?_ hG
  filter_upwards [eventually_ne_nhds hζ] with ρ hρ0
  have hb2 : MemLp b (ENNReal.ofReal 2) volume := by simpa using hb
  have hd : MemLp (fun z => ‖ρ‖ • c (ρ * z) - ‖ζ‖ • c (ζ * z)) 2 volume :=
    (memLp_dil hc ρ hρ0).sub (memLp_dil hc ζ hζ)
  have hd2 : MemLp (fun z => ‖ρ‖ • c (ρ * z) - ‖ζ‖ • c (ζ * z)) (ENNReal.ofReal 2) volume := by
    simpa using hd
  have hint : Integrable (fun z => ‖b z‖ * ‖‖ρ‖ • c (ρ * z) - ‖ζ‖ • c (ζ * z)‖) volume :=
    hb.norm.integrable_mul hd.norm
  have hpt : ∀ z, ‖⟪b z, ((‖ρ‖ : ℝ) : ℂ) • c (ρ * z)⟫_ℂ - ⟪b z, ((‖ζ‖ : ℝ) : ℂ) • c (ζ * z)⟫_ℂ‖ ≤
      ‖b z‖ * ‖‖ρ‖ • c (ρ * z) - ‖ζ‖ • c (ζ * z)‖ := by
    intro z
    rw [← inner_sub_right, Complex.coe_smul, Complex.coe_smul]
    exact norm_inner_le_norm _ _
  calc ∫ z, ‖⟪b z, ((‖ρ‖ : ℝ) : ℂ) • c (ρ * z)⟫_ℂ - ⟪b z, ((‖ζ‖ : ℝ) : ℂ) • c (ζ * z)⟫_ℂ‖
      ≤ ∫ z, ‖b z‖ * ‖‖ρ‖ • c (ρ * z) - ‖ζ‖ • c (ζ * z)‖ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) hint
          (Filter.Eventually.of_forall hpt)
    _ ≤ K * (∫ z, ‖‖ρ‖ • c (ρ * z) - ‖ζ‖ • c (ζ * z)‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
        integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hb2 hd2
    _ = K * (∫ z, ‖‖ρ‖ • c (ρ * z) - ‖ζ‖ • c (ζ * z)‖ ^ 2) ^ (1 / (2 : ℝ)) := by
        congr 2
        congr 1
        funext z
        exact Real.rpow_two _

theorem tendsto_dil_real (ab : ℂ → ℝ) (hab : MemLp ab 2 volume) :
    Tendsto (fun ρ : ℂ => ∫ z, (‖ρ‖ * ab (ρ * z) - ab z) ^ 2) (𝓝 1) (𝓝 0) := by
  have h := tendsto_dil ab hab 1 one_ne_zero
  refine h.congr fun ρ => ?_
  congr 1
  funext z
  rw [Real.norm_eq_abs, sq_abs, norm_one, one_smul, one_mul, smul_eq_mul]

end dil

end

end Formalism.FourierDecayAlt.P.PBK
