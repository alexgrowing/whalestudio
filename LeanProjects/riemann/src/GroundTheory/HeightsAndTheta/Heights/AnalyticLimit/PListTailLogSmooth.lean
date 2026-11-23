import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StListTailLog
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StListTailLogSmooth
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.SystemIndependence
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory Filter Topology Set
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential mInt MIntegrable)
open ReciprocityTheory.AnForm.A (coordDiv)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

noncomputable section

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}

theorem regChartData_continuousOn_r (R : RegChartData A) : ContinuousOn R.r R.Yo := by
  intro x hx
  obtain ⟨j, hxs, hxW⟩ := R.cover x
  have hW : R.ψ j x ∈ R.W j :=
    R.closure_W'_subset j (subset_closure (R.closure_W''_subset j (subset_closure hxW)))
  have hnd : R.ψ j x ∉ coordDiv (R.S j) :=
    (R.mem_Yo_iff j _ hW).1 (by rw [(R.ψ j).left_inv hxs]; exact hx)
  have hne : ∀ i ∈ R.S j, R.ψ j x i ≠ 0 := fun i hi h0 => hnd ⟨i, hi, h0⟩
  let g : (Fin D → ℂ) → ℝ := fun z => Real.exp 1 + R.f j z - ∑ i ∈ R.S j, Real.log (‖z i‖ ^ 2)
  have hg : ContinuousAt g (R.ψ j x) := by
    refine (continuousAt_const.add ((R.f_cont j).continuousAt ((R.isOpen_kappaOpenNeighbourhood j).mem_nhds hW))).sub
      (tendsto_finsetSum (R.S j) fun i hi => ?_)
    exact ((continuous_apply i).continuousAt.norm.pow 2).log (pow_pos (norm_pos_iff.2 (hne i hi)) 2).ne'
  have hz : ∀ᶠ z in 𝓝 (R.ψ j x), z ∈ R.W j ∧ z ∉ coordDiv (R.S j) := by
    refine (show ∀ᶠ z in 𝓝 (R.ψ j x), z ∈ R.W j from (R.isOpen_kappaOpenNeighbourhood j).mem_nhds hW).and ?_
    have : ∀ᶠ z in 𝓝 (R.ψ j x), ∀ i ∈ R.S j, z i ≠ 0 := (eventually_all_finset _).2 fun i hi =>
      (continuous_apply i).continuousAt.eventually_ne (hne i hi)
    exact this.mono fun z hz ⟨i, hi, h0⟩ => hz i hi h0
  have hev : R.r =ᶠ[𝓝 x] g ∘ R.ψ j := by
    filter_upwards [((R.ψ j).continuousAt hxs).eventually hz, (R.ψ j).open_source.mem_nhds hxs]
      with y hy hys
    have := R.r_chart j (R.ψ j y) ⟨hy.1, hy.2⟩
    rw [(R.ψ j).left_inv hys] at this
    exact this
  exact ((hg.comp ((R.ψ j).continuousAt hxs)).congr hev.symm).continuousWithinAt

theorem regChartData_C_nonneg (R : RegChartData A) {x : X} (hx : x ∈ R.Yo) : 0 ≤ R.C := by
  by_contra h
  have h1 := R.le_φ x hx
  have h2 := R.φ_le x hx
  have h3 : 0 ≤ Real.log (R.r x) := Real.log_nonneg (R.one_le_r x hx)
  nlinarith

def regChartShift (R : RegChartData A) : RegChartData A :=
  { R with
    r := fun x => R.r x + (Real.exp 1 - 1)
    f := fun j z => R.f j z + (Real.exp 1 - 1)
    f_cont := fun j => (R.f_cont j).add continuousOn_const
    f_bdd := fun j => by
      obtain ⟨B, hB⟩ := R.f_bdd j
      exact ⟨B + |Real.exp 1 - 1|, fun z hz => (abs_add_le _ _).trans (by linarith [hB z hz])⟩
    r_chart := fun j z hz => by rw [R.r_chart j z hz]; ring
    one_le_r := fun x hx => by
      have := R.one_le_r x hx
      have := Real.add_one_le_exp (0 : ℝ)
      rw [Real.exp_zero] at this
      linarith [Real.add_one_le_exp (1 : ℝ)]
    le_φ := fun x hx => by
      have hC := regChartData_C_nonneg R hx
      have h1 := R.one_le_r x hx
      have : Real.log (R.r x) ≤ Real.log (R.r x + (Real.exp 1 - 1)) :=
        Real.log_le_log (by linarith) (by linarith [Real.add_one_le_exp (1 : ℝ)])
      nlinarith [R.le_φ x hx]
    grad := fun j z hz => by
      have hx : (R.ψ j).symm z ∈ R.Yo := (R.mem_Yo_iff j z hz.1).2 hz.2
      have hC := regChartData_C_nonneg R hx
      have h1 := R.one_le_r _ hx
      have he : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      refine (R.grad j z hz).trans (mul_le_mul (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by linarith) (by linarith) hC) hC)
        (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos _).le (by positivity)) }

theorem tailLogBound_of_le [CompactSpace X] [T2Space X] {Yo : Set X} (hYo : IsOpen Yo)
    {r r' : X → ℝ} (hr : ContinuousOn r Yo) (hle : ∀ x ∈ Yo, r x ≤ r' x) {T : Fin D → LocPot X}
    (hpot : ∀ i, IsPotential A (T i)) (hnn : ∀ i, FormNonneg A Yo (T i)) {CE : ℝ}
    (h : TailLogBound A Yo r' T CE) : TailLogBound A Yo r T CE := by
  intro R₀ hR₀
  obtain ⟨hI, hB⟩ := h R₀ hR₀
  have he : (1 : ℝ) ≤ R₀ := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hR₀
  set gs := (tail Yo r R₀).indicator fun x => Real.log (r x) with hgs
  set gb := (tail Yo r' R₀).indicator fun x => Real.log (r' x) with hgb
  have hg : ∀ x, 0 ≤ gs x ∧ gs x ≤ gb x := by
    intro x
    by_cases hx : x ∈ tail Yo r R₀
    · have hx' : x ∈ tail Yo r' R₀ := ⟨hx.1, hx.2.trans (hle x hx.1)⟩
      rw [hgs, hgb, indicator_of_mem hx, indicator_of_mem hx']
      exact ⟨Real.log_nonneg (he.trans hx.2),
        Real.log_le_log (by linarith [hx.2]) (hle x hx.1)⟩
    · rw [hgs, indicator_of_notMem hx]
      refine ⟨le_rfl, ?_⟩
      by_cases hx' : x ∈ tail Yo r' R₀
      · rw [hgb, indicator_of_mem hx']
        exact Real.log_nonneg (he.trans hx'.2)
      · rw [hgb, indicator_of_notMem hx']
  have hI' : MIntegrable A T gs := by
    intro k K hK hKc
    set U := (A.chart k).target ∩ (A.chart k).symm ⁻¹' Yo with hUdef
    have hU : IsOpen U := (A.chart k).isOpen_inter_preimage_symm hYo
    have hF : ContinuousOn (fun y => r ((A.chart k).symm y)) U :=
      hr.comp ((A.chart k).continuousOn_symm.mono inter_subset_left) fun y hy => hy.2
    set Ms := U ∩ (fun y => r ((A.chart k).symm y)) ⁻¹' Ici R₀ with hMs
    have hM : MeasurableSet Ms := by
      have ho := hF.isOpen_inter_preimage hU (isOpen_Iio (a := R₀))
      have e : Ms = U \ (U ∩ (fun y => r ((A.chart k).symm y)) ⁻¹' Iio R₀) := by
        ext y
        constructor
        · rintro ⟨hu, hge⟩
          exact ⟨hu, fun hm => (not_le.2 (show r ((A.chart k).symm y) < R₀ from hm.2)) (show R₀ ≤ r ((A.chart k).symm y) from hge)⟩
        · rintro ⟨hu, hn⟩
          exact ⟨hu, show R₀ ≤ r ((A.chart k).symm y) from not_lt.1 fun hlt => hn ⟨hu, hlt⟩⟩
      rw [e]
      exact hU.measurableSet.diff ho.measurableSet
    have hlog : ContinuousOn (fun y => Real.log (r ((A.chart k).symm y))) Ms :=
      (hF.mono inter_subset_left).log fun y hy => by
        have : R₀ ≤ r ((A.chart k).symm y) := hy.2
        exact (by linarith : (0 : ℝ) < _).ne'
    have hcongr : (fun y => gs ((A.chart k).symm y)) =ᵐ[volume.restrict K]
        Ms.indicator fun y => Real.log (r ((A.chart k).symm y)) := by
      refine ae_restrict_of_forall_mem hKc.measurableSet fun y hy => ?_
      have hyt := hK hy
      by_cases hc : (A.chart k).symm y ∈ tail Yo r R₀
      · show (tail Yo r R₀).indicator (fun x => Real.log (r x)) ((A.chart k).symm y) = _
        rw [indicator_of_mem hc, indicator_of_mem (show y ∈ Ms from ⟨⟨hyt, hc.1⟩, hc.2⟩)]
      · show (tail Yo r R₀).indicator (fun x => Real.log (r x)) ((A.chart k).symm y) = _
        rw [indicator_of_notMem hc,
          indicator_of_notMem (show y ∉ Ms from fun hm => hc ⟨hm.1.2, hm.2⟩)]
    have hmeas : AEStronglyMeasurable
        (fun y => gs ((A.chart k).symm y) * ReciprocityTheory.AnForm.M.locDens A T k y) (volume.restrict K) :=
      (((aestronglyMeasurable_indicator_iff hM).2 (hlog.aestronglyMeasurable hM)).congr
        hcongr.symm).mul
        (((ReciprocityTheory.AnForm.M.locDensCont A T hpot k).mono hK).aestronglyMeasurable hKc.measurableSet)
    refine (hI k K hK hKc).norm.mono' hmeas (ae_of_all _ fun y => ?_)
    simp only [norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [Real.norm_of_nonneg (hg _).1, Real.norm_of_nonneg ((hg _).1.trans (hg _).2)]
    exact (hg _).2
  refine ⟨hI', ?_⟩
  have hlin := ReciprocityTheory.AnForm.M.mIntLinear A T hpot (-1) gs gb hI' hI
  have h0 := SystemIndependence.mInt_nonneg_on A Yo T hpot hnn (fun x => -1 * gs x + gb x)
    (fun x => by linarith [hg x]) (fun x hx => by
      rw [hgs, hgb, indicator_of_notMem (fun h => hx h.1), indicator_of_notMem (fun h => hx h.1)]
      ring)
  linarith

theorem ListTailLogSmooth.proof (h : ListTailLog.Statement) : ListTailLogSmooth.Statement := by
  intro D X _ _ _ A R Om C₁
  have he1 : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  obtain ⟨CE, hCE⟩ := h D A (regChartShift R) (fun x hx => by
    show Real.exp 1 ≤ R.r x + (Real.exp 1 - 1)
    linarith [R.one_le_r x hx]) Om (max C₁ 0)
  refine ⟨CE, fun th u hT => ?_⟩
  have hpot : ∀ i, IsPotential A (potForm (th i) (u i)) := fun i =>
    ReciprocityTheory.AnForm.M.isPotentialAdd A _ _ (hT i).1.th_pot
      (ReciprocityTheory.AnForm.M.isPotential_ofFun A _ (hT i).2)
  refine tailLogBound_of_le R.isOpen_Yo (regChartData_continuousOn_r R)
    (r' := (regChartShift R).r) (fun x _ => by show R.r x ≤ R.r x + (Real.exp 1 - 1); linarith)
    hpot (fun i => (hT i).1.nonneg) (hCE th u fun j => ?_)
  exact { (hT j).1 with
    le_u := fun x hx => by
      have h1 := R.one_le_r x hx
      have hl : Real.log (R.r x) ≤ Real.log (R.r x + (Real.exp 1 - 1)) :=
        Real.log_le_log (by linarith) (by linarith)
      have h0 := Real.log_nonneg h1
      have hu := (hT j).1.le_u x hx
      show -(max C₁ 0 * Real.log (R.r x + (Real.exp 1 - 1))) ≤ u j x
      nlinarith [le_max_left C₁ 0, le_max_right C₁ 0] }

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
