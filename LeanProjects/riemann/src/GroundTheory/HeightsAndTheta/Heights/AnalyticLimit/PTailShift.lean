import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StTailShift
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.IntegrableOnTargetOfMIntegrable
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot mInt MIntegrable locDens)

theorem log_le_of_abs_sub_le {B a b : ℝ} (hb : Real.exp 1 ≤ b) (ha : 0 < a) (hab : |a - b| ≤ B) :
    Real.log a ≤ (1 + max B 0) * Real.log b := by
  have hb0 : 0 < b := lt_of_lt_of_le (Real.exp_pos 1) hb
  have hlb : 1 ≤ Real.log b := by rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hb
  have hB : 0 ≤ max B 0 := le_max_right _ _
  have hb1 : 1 ≤ b := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hb
  have h1 : a ≤ b * (1 + max B 0) := by
    have := (abs_le.1 hab).2
    have := le_max_left B 0
    nlinarith [mul_nonneg (sub_nonneg.2 hb1) hB]
  calc Real.log a ≤ Real.log (b * (1 + max B 0)) := Real.log_le_log ha h1
    _ = Real.log b + Real.log (1 + max B 0) := Real.log_mul hb0.ne' (by positivity)
    _ ≤ Real.log b + max B 0 := by
      linarith [Real.log_le_sub_one_of_pos (show 0 < 1 + max B 0 by positivity)]
    _ ≤ (1 + max B 0) * Real.log b := by nlinarith [mul_nonneg hB (sub_nonneg.2 hlb)]

theorem TailShift.proof : TailShift.Statement := by
  intro D B CE
  set Bp := max B 0 with hBpdef
  set R1 := max (Real.exp 1 + Bp) (2 * Bp)
  refine ⟨2 * (1 + Bp) * max CE 0 * R1, ?_⟩
  intro X _ _ _ A Yo r r' T hYo hr hr' hre hr'e hB hdens hT
  let : MeasurableSpace X := borel X
  have : BorelSpace X := ⟨rfl⟩
  have he := Real.exp_pos 1
  have hBp : 0 ≤ Bp := le_max_right _ _
  have hlog : ∀ x ∈ Yo, Real.log (r x) ≤ (1 + Bp) * Real.log (r' x) := fun x hx =>
    log_le_of_abs_sub_le (hr'e x hx) (lt_of_lt_of_le he (hre x hx)) (hB x hx)
  have hl' : ∀ x ∈ Yo, 1 ≤ Real.log (r' x) := fun x hx => by
    rw [← Real.log_exp 1]; exact Real.log_le_log he (hr'e x hx)
  have hl : ∀ x ∈ Yo, 1 ≤ Real.log (r x) := fun x hx => by
    rw [← Real.log_exp 1]; exact Real.log_le_log he (hre x hx)

  have key : ∀ R₀ R', Real.exp 1 ≤ R' → (∀ x ∈ Yo, R₀ ≤ r x → R' ≤ r' x) →
      mInt A T ((tail Yo r R₀).indicator fun x => Real.log (r x)) ≤
        (1 + Bp) * mInt A T ((tail Yo r' R').indicator fun x => Real.log (r' x)) := by
    intro R₀ R' hR' hsub
    refine mInt_le_mul_of_le A T Yo (hT R' hR').1 hdens (fun x => ?_)
      (fun x hx => Set.indicator_of_notMem (fun h => hx h.1) _)
      (fun x hx => Set.indicator_of_notMem (fun h => hx h.1) _) (fun x hx => ?_)
    · by_cases h : x ∈ tail Yo r R₀
      · rw [Set.indicator_of_mem h]; linarith [hl x h.1]
      · rw [Set.indicator_of_notMem h]
    · by_cases h : R₀ ≤ r x
      · rw [Set.indicator_of_mem (show x ∈ tail Yo r R₀ from ⟨hx, h⟩),
          Set.indicator_of_mem (show x ∈ tail Yo r' R' from ⟨hx, hsub x hx h⟩)]
        exact hlog x hx
      · rw [Set.indicator_of_notMem (show x ∉ tail Yo r R₀ from fun h' => h h'.2)]
        by_cases h' : R' ≤ r' x
        · rw [Set.indicator_of_mem (show x ∈ tail Yo r' R' from ⟨hx, h'⟩)]
          nlinarith [hl' x hx]
        · rw [Set.indicator_of_notMem (show x ∉ tail Yo r' R' from fun h'' => h' h''.2)]; simp

  have hint : ∀ R₀, MIntegrable A T ((tail Yo r R₀).indicator fun x => Real.log (r x)) := by
    intro R₀ j K hK hKc
    have htm : MeasurableSet (tail Yo r R₀) := by
      have : tail Yo r R₀ = Yo \ (Yo ∩ r ⁻¹' Set.Iio R₀) := by
        ext x
        simp only [tail, Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_inter_iff, Set.mem_preimage,
          Set.mem_Iio, not_and, not_lt]
        exact ⟨fun h => ⟨h.1, fun _ => h.2⟩, fun h => ⟨h.1, h.2 h.1⟩⟩
      rw [this]
      exact hYo.measurableSet.diff (hr.isOpen_inter_preimage hYo isOpen_Iio).measurableSet
    have hGc : ContinuousOn (fun x => Real.log (r x) / Real.log (r' x)) (tail Yo r R₀) :=
      ((hr.log fun x hx => (lt_of_lt_of_le he (hre x hx)).ne').div
        (hr'.log fun x hx => (lt_of_lt_of_le he (hr'e x hx)).ne')
        fun x hx => (lt_of_lt_of_le one_pos (hl' x hx)).ne').mono fun x hx => hx.1
    classical
    have hGm : Measurable ((tail Yo r R₀).indicator fun x => Real.log (r x) / Real.log (r' x)) := by
      have := hGc.measurable_piecewise (continuousOn_const (c := (0 : ℝ))) htm
      convert this using 1
      funext x
      simp [Set.indicator, Set.piecewise]
    have hT' : MeasurableSet (A.chart j).target := (A.chart j).open_target.measurableSet
    have hsm : AEMeasurable (fun y => (tail Yo r R₀).indicator
        (fun x => Real.log (r x) / Real.log (r' x)) ((A.chart j).symm y)) (volume.restrict K) :=
      (hGm.comp_aemeasurable ((A.chart j).continuousOn_symm.aemeasurable hT')).mono_measure
        (Measure.restrict_mono hK le_rfl)
    have hid : ∀ x, (tail Yo r R₀).indicator (fun x => Real.log (r x)) x =
        (tail Yo r R₀).indicator (fun x => Real.log (r x) / Real.log (r' x)) x *
          (tail Yo r' (Real.exp 1)).indicator (fun x => Real.log (r' x)) x := by
      intro x
      by_cases h : x ∈ tail Yo r R₀
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h,
          Set.indicator_of_mem (show x ∈ tail Yo r' (Real.exp 1) from ⟨h.1, hr'e x h.1⟩),
          div_mul_cancel₀ _ (lt_of_lt_of_le one_pos (hl' x h.1)).ne']
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]
    have e1 : (fun y => (tail Yo r R₀).indicator (fun x => Real.log (r x)) ((A.chart j).symm y) *
        locDens A T j y) = fun y => (tail Yo r R₀).indicator
          (fun x => Real.log (r x) / Real.log (r' x)) ((A.chart j).symm y) *
          ((tail Yo r' (Real.exp 1)).indicator (fun x => Real.log (r' x)) ((A.chart j).symm y) *
            locDens A T j y) := by
      funext y
      rw [hid, mul_assoc]
    rw [e1]
    refine Integrable.bdd_mul (c := 1 + Bp) ((hT (Real.exp 1) le_rfl).1 j K hK hKc)
      hsm.aestronglyMeasurable (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs]
    by_cases h : (A.chart j).symm y ∈ tail Yo r R₀
    · rw [Set.indicator_of_mem h]
      have h1 := hl' _ h.1
      have h3 := hl _ h.1
      rw [abs_of_nonneg (div_nonneg (by linarith) (by linarith)), div_le_iff₀ (by linarith)]
      exact hlog _ h.1
    · rw [Set.indicator_of_notMem h, abs_zero]
      linarith

  intro R₀ hR₀
  refine ⟨hint R₀, ?_⟩
  have hlR : 1 ≤ Real.log R₀ := by rw [← Real.log_exp 1]; exact Real.log_le_log he hR₀
  have hR0 : 0 < R₀ := lt_of_lt_of_le he hR₀
  have hR1a : Real.exp 1 + Bp ≤ R1 := le_max_left _ _
  have hR1b : 2 * Bp ≤ R1 := le_max_right _ _
  have hCE : CE ≤ max CE 0 := le_max_left _ _
  have hCE0 : 0 ≤ max CE 0 := le_max_right _ _
  have he1 : 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hL0 : 0 ≤ Real.log R₀ ^ (D + 1) := pow_nonneg (by linarith) _
  have hL1 : 1 ≤ Real.log R₀ ^ (D + 1) := one_le_pow₀ hlR
  have hBp1 : 0 ≤ 1 + Bp := by linarith
  by_cases hbig : R1 ≤ R₀
  · have hR' : Real.exp 1 ≤ R₀ - Bp := by linarith
    have hpos : 0 < R₀ - Bp := by linarith
    refine (key R₀ (R₀ - Bp) hR' fun x hx h => ?_).trans ?_
    · have := (abs_le.1 (hB x hx)).2
      linarith [le_max_left B 0]
    have hb := (hT (R₀ - Bp) hR').2
    have hlog1 : 0 ≤ Real.log (R₀ - Bp) := Real.log_nonneg (by linarith)
    have hpow : Real.log (R₀ - Bp) ^ (D + 1) ≤ Real.log R₀ ^ (D + 1) :=
      pow_le_pow_left₀ hlog1 (Real.log_le_log hpos (by linarith)) _
    have s1 : CE * Real.log (R₀ - Bp) ^ (D + 1) / (R₀ - Bp) ≤
        max CE 0 * Real.log R₀ ^ (D + 1) / (R₀ - Bp) :=
      div_le_div_of_nonneg_right (mul_le_mul hCE hpow (pow_nonneg hlog1 _) hCE0) hpos.le
    have s2 : max CE 0 * Real.log R₀ ^ (D + 1) / (R₀ - Bp) ≤
        max CE 0 * Real.log R₀ ^ (D + 1) * 2 / R₀ := by
      rw [div_le_div_iff₀ hpos hR0]
      nlinarith [mul_nonneg (mul_nonneg hCE0 hL0) (show 0 ≤ 2 * (R₀ - Bp) - R₀ by linarith)]
    have s3 : 2 * (1 + Bp) * max CE 0 * Real.log R₀ ^ (D + 1) ≤
        2 * (1 + Bp) * max CE 0 * R1 * Real.log R₀ ^ (D + 1) := by
      have h0 : 0 ≤ 2 * (1 + Bp) * max CE 0 * Real.log R₀ ^ (D + 1) := by positivity
      nlinarith [mul_nonneg h0 (show 0 ≤ R1 - 1 by linarith)]
    calc (1 + Bp) * mInt A T ((tail Yo r' (R₀ - Bp)).indicator fun x => Real.log (r' x))
        ≤ (1 + Bp) * (max CE 0 * Real.log R₀ ^ (D + 1) * 2 / R₀) :=
          mul_le_mul_of_nonneg_left (hb.trans (s1.trans s2)) hBp1
      _ = 2 * (1 + Bp) * max CE 0 * Real.log R₀ ^ (D + 1) / R₀ := by ring
      _ ≤ 2 * (1 + Bp) * max CE 0 * R1 * Real.log R₀ ^ (D + 1) / R₀ :=
          div_le_div_of_nonneg_right s3 hR0.le
  · replace hbig := not_le.1 hbig
    refine (key R₀ (Real.exp 1) le_rfl fun x hx _ => hr'e x hx).trans ?_
    have hb := (hT (Real.exp 1) le_rfl).2
    rw [Real.log_exp, one_pow, mul_one] at hb
    have s1 : CE / Real.exp 1 ≤ max CE 0 := by
      rw [div_le_iff₀ he]; nlinarith [mul_nonneg hCE0 (show 0 ≤ Real.exp 1 - 1 by linarith)]
    have hZ : 0 ≤ (1 + Bp) * max CE 0 := mul_nonneg hBp1 hCE0
    have s2 : R₀ ≤ 2 * R1 * Real.log R₀ ^ (D + 1) := by nlinarith
    calc (1 + Bp) * mInt A T ((tail Yo r' (Real.exp 1)).indicator fun x => Real.log (r' x))
        ≤ (1 + Bp) * max CE 0 := mul_le_mul_of_nonneg_left (hb.trans s1) hBp1
      _ ≤ 2 * (1 + Bp) * max CE 0 * R1 * Real.log R₀ ^ (D + 1) / R₀ := by
          rw [le_div_iff₀ hR0]
          nlinarith [mul_le_mul_of_nonneg_left s2 hZ]

end GroundTheory.Heights₂.Heights.AnalyticLimit
