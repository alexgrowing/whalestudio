import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxB
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNsqCanonicalAddChartPartStatement
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.GlueDist

theorem sq_norm_smoothSection_sub_glued_le : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La) (F0 : ι → Y → ℂ) (u : Fin C.m → V n → ℂ), A.IsSSec (A.kap + la) F0 → (∀ a, DifferentiableOn ℂ (u a) (ball (C.c a) (C.r a))) → n0 A la (F0 - glue C la u) ≤ (C.m : ℝ≥0∞) * ∑ a, ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal (‖F0 (C.idx a) ((A.chart (C.idx a)).symm v) - u a v‖ ^ 2 * Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) := by
  intro n Y _ _ _ _ _ ι La _ A C la F0 u hF hu
  classical
  set L := A.kap + la with hL

  set D : Fin C.m → ι → Y → ℂ := fun a j y =>
    F0 j y - A.g L j (C.idx a) y * u a (A.chart (C.idx a) y) with hD
  set S : Fin C.m → Set Y := fun a =>
    (A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' ball (C.c a) (C.r a) with hS
  have hSo : ∀ a, IsOpen (S a) := fun a =>
    (A.chart (C.idx a)).isOpen_inter_preimage isOpen_ball
  have hsec : ∀ a, ∀ y ∈ (A.chart (C.idx a)).source, ∀ j, y ∈ (A.chart j).source →
      D a j y = A.g L j (C.idx a) y * D a (C.idx a) y := by
    intro a y hy j hj
    simp only [hD]
    rw [hF.2 j (C.idx a) y hj hy, A.g_self L (C.idx a) hy]
    ring
  have hchart : ∀ a, ∀ y ∈ (A.chart (C.idx a)).source,
      A.nsq L (D a) y = ‖F0 (C.idx a) y - u a (A.chart (C.idx a) y)‖ ^ 2 *
        Real.exp (-A.ph L (C.idx a) y) := by
    intro a y hy
    rw [A.nsq_chart L (D a) (C.idx a) hy (hsec a y hy _ (A.mem_pick y))]
    simp only [hD, A.g_self L (C.idx a) hy, one_mul]

  have hsum1 : ∀ y, ∑ a, (C.chi a y : ℂ) = 1 := by
    intro y; rw [← Complex.ofReal_sum, C.sum_one y, Complex.ofReal_one]
  have hG : F0 - glue C la u = fun j y => ∑ a, (C.chi a y : ℂ) * D a j y := by
    funext j y
    simp only [Pi.sub_apply, glue, hD, mul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, hsum1 y, one_mul]
    congr 1
    exact Finset.sum_congr rfl (fun a _ => by ring)
  have hchi1 : ∀ a y, C.chi a y ≤ 1 := by
    intro a y
    rw [← C.sum_one y]
    exact Finset.single_le_sum (fun b _ => C.nonneg b y) (Finset.mem_univ a)

  have hpt : ∀ y, A.nsq L (F0 - glue C la u) y ≤
      (C.m : ℝ) * ∑ a, (S a).indicator (A.nsq L (D a)) y := by
    intro y
    rw [hG]
    refine (A.nsq_sum_le L Finset.univ (fun a j y => (C.chi a y : ℂ) * D a j y) y).trans ?_
    rw [Finset.card_univ, Fintype.card_fin]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => ?_) (Nat.cast_nonneg _)
    have he : A.nsq L (fun j y => (C.chi a y : ℂ) * D a j y) y = C.chi a y ^ 2 * A.nsq L (D a) y := by
      unfold WeightedAtlas.nsq
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (C.nonneg a y)]
      ring
    rw [he]
    by_cases h0 : C.chi a y = 0
    · rw [h0]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
      exact Set.indicator_nonneg (fun x _ => A.nsq_nonneg L (D a) x) y
    · have hyS : y ∈ S a := C.supp a (subset_tsupport _ h0)
      rw [Set.indicator_of_mem hyS]
      have h2 : C.chi a y ^ 2 ≤ 1 := pow_le_one₀ (C.nonneg a y) (hchi1 a y)
      nlinarith [A.nsq_nonneg L (D a) y]

  have hF0c : ∀ i, ContinuousOn (F0 i) (A.chart i).source := by
    intro i
    have h1 : ContinuousOn (F0 i ∘ (A.chart i).symm) (A.chart i).target := (hF.1 i).continuousOn
    refine (h1.comp (A.chart i).continuousOn (fun x hx => (A.chart i).map_source hx)).congr
      (fun x hx => ?_)
    simp [Function.comp, (A.chart i).left_inv hx]
  have hcont : ∀ a, ContinuousOn (fun y => ENNReal.ofReal (A.nsq L (D a) y)) (S a) := by
    intro a
    refine ENNReal.continuous_ofReal.comp_continuousOn ?_
    have hu' : ContinuousOn (fun y => u a (A.chart (C.idx a) y)) (S a) :=
      (hu a).continuousOn.comp ((A.chart (C.idx a)).continuousOn.mono Set.inter_subset_left)
        (fun y hy => hy.2)
    have hc : ContinuousOn (fun y => ‖F0 (C.idx a) y - u a (A.chart (C.idx a) y)‖ ^ 2 *
        Real.exp (-A.ph L (C.idx a) y)) (S a) :=
      ((((hF0c (C.idx a)).mono Set.inter_subset_left).sub hu').norm.pow 2).mul
        ((A.continuousOn_ph L (C.idx a)).mono Set.inter_subset_left).neg.rexp
    exact hc.congr (fun y hy => hchart a y hy.1)
  have hmeas : ∀ a, AEMeasurable ((S a).indicator (fun y => ENNReal.ofReal (A.nsq L (D a) y))) A.mu :=
    fun a => (aemeasurable_indicator_iff (hSo a).measurableSet).2
      ((hcont a).aemeasurable (hSo a).measurableSet)

  have hpiece : ∀ a, ∫⁻ y in S a, ENNReal.ofReal (A.nsq L (D a) y) ∂A.mu =
      ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal (‖F0 (C.idx a) ((A.chart (C.idx a)).symm v) - u a v‖ ^ 2 *
        Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) := by
    intro a
    have hWt : ball (C.c a) (C.r a) ⊆ (A.chart (C.idx a)).target :=
      ball_subset_closedBall.trans (C.sub a)
    have heq : ∀ v ∈ ball (C.c a) (C.r a),
        D a (C.idx a) ((A.chart (C.idx a)).symm v) = F0 (C.idx a) ((A.chart (C.idx a)).symm v) - u a v := by
      intro v hv
      have hvt := hWt hv
      simp only [hD, A.g_self L (C.idx a) ((A.chart (C.idx a)).map_target hvt),
        (A.chart (C.idx a)).right_inv hvt, one_mul]
    have hae : AEMeasurable (D a (C.idx a) ∘ (A.chart (C.idx a)).symm) (volume.restrict (ball (C.c a) (C.r a))) := by
      have hc : ContinuousOn (fun v => F0 (C.idx a) ((A.chart (C.idx a)).symm v) - u a v) (ball (C.c a) (C.r a)) :=
        (((hF.1 (C.idx a)).continuousOn.mono hWt).sub (hu a).continuousOn)
      exact (hc.congr (fun v hv => heq v hv)).aemeasurable measurableSet_ball
    rw [GlobalTheory.T.lintegral_nsq_canonical_add_chart_part n Y ι La A la (C.idx a) (ball (C.c a) (C.r a)) (D a) measurableSet_ball hWt
      (fun y hy _ => hsec a y hy _ (A.mem_pick y)) hae]
    refine setLIntegral_congr_fun measurableSet_ball (fun v hv => ?_)
    rw [heq v hv]

  unfold n0
  calc ∫⁻ y, ENNReal.ofReal (A.nsq L (F0 - glue C la u) y) ∂A.mu
      ≤ ∫⁻ y, (C.m : ℝ≥0∞) * ∑ a, (S a).indicator (fun y => ENNReal.ofReal (A.nsq L (D a) y)) y ∂A.mu := by
        refine lintegral_mono fun y => ?_
        refine (ENNReal.ofReal_le_ofReal (hpt y)).trans (le_of_eq ?_)
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
          ENNReal.ofReal_sum_of_nonneg (fun a _ => Set.indicator_nonneg (fun x _ => A.nsq_nonneg L (D a) x) y)]
        congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        by_cases hy : y ∈ S a
        · simp [Set.indicator_of_mem hy]
        · simp [Set.indicator_of_notMem hy]
    _ = (C.m : ℝ≥0∞) * ∑ a, ∫⁻ y in S a, ENNReal.ofReal (A.nsq L (D a) y) ∂A.mu := by
        rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _), lintegral_finset_sum' _ (fun a _ => hmeas a)]
        congr 1
        exact Finset.sum_congr rfl fun a _ => lintegral_indicator (hSo a).measurableSet _
    _ = _ := by
        congr 1
        exact Finset.sum_congr rfl fun a _ => hpiece a

end GlobalTheory.GlueDist
