import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialChartContDiffAtTwo
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
open Filter Topology Set Metric MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.Mean4O
open scoped ContDiff

namespace GlobalTheory.Mean4O

theorem locallyIntegrableOn_of_log_bound (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (Z : Set X)
    (r : X → ℝ) (Om : LocPot X) (h : IsBd A Z r Om) (u : X → ℝ) (C : ℝ) (hu : A.SmoothOn Zᶜ u)
    (hb : ∀ x, x ∉ Z → |u x| ≤ C * Real.log (r x)) (j : Fin A.n) :
    MeasureTheory.LocallyIntegrableOn (u ∘ (A.chart j).symm) (A.chart j).target MeasureTheory.volume := by
  obtain ⟨hZ, hnull, hpot, hpos, -, hr, -, hint, -⟩ := h
  have hD := locDensPos A (fun _ => Om) (fun _ => hpot) (fun _ => hpos) j
  have hDc := locDensCont A (fun _ => Om) (fun _ => hpot) j
  rw [locallyIntegrableOn_iff (A.chart j).open_target.isLocallyClosed]
  intro K hK hKc
  have hinv : ContinuousOn (fun y => |C| * (locDens A (fun _ => Om) j y)⁻¹) K :=
    continuousOn_const.mul ((hDc.mono hK).inv₀ fun y hy => (hD y (hK hy)).ne')
  have h1 := (hint j K hK hKc).mul_continuousOn hinv hKc
  have hVo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Zᶜ) :=
    (A.chart j).isOpen_inter_preimage_symm hZ.isOpen_compl
  have hae : ∀ᵐ y ∂(volume : Measure (Fin e → ℂ)), y ∉ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Z :=
    measure_eq_zero_iff_ae_notMem.1 (hnull j)
  have hKV : K =ᵐ[volume] (K ∩ ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Zᶜ) : Set _) := by
    filter_upwards [hae] with y hy
    refine propext ⟨fun hyK => ⟨hyK, hK hyK, fun hz => hy ⟨hK hyK, hz⟩⟩, fun hyK => hyK.1⟩
  refine Integrable.mono' h1 ?_ ?_
  · rw [Measure.restrict_congr_set hKV]
    exact ((hu j).continuousOn.mono inter_subset_right).aestronglyMeasurable
      (hKc.measurableSet.inter hVo.measurableSet)
  · rw [ae_restrict_iff' hKc.measurableSet]
    filter_upwards [hae] with y hy hyK
    have hz : (A.chart j).symm y ∉ Z := fun hz => hy ⟨hK hyK, hz⟩
    have hr1 := hr _ hz
    have hr0 : 1 ≤ r ((A.chart j).symm y) := le_trans (Real.one_le_exp zero_le_one) hr1
    have hc : cut Z univ r ((A.chart j).symm y) = r ((A.chart j).symm y) :=
      indicator_of_mem (show _ ∈ univ ∩ Zᶜ from ⟨mem_univ _, hz⟩) _
    have hDy := (hD y (hK hyK)).ne'
    have he : cut Z univ r ((A.chart j).symm y) * locDens A (fun _ => Om) j y *
        (|C| * (locDens A (fun _ => Om) j y)⁻¹) = |C| * r ((A.chart j).symm y) := by
      rw [hc]; field_simp
    rw [he, Function.comp_apply, Real.norm_eq_abs]
    calc |u ((A.chart j).symm y)| ≤ C * Real.log (r ((A.chart j).symm y)) := hb _ hz
      _ ≤ |C| * Real.log (r ((A.chart j).symm y)) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (Real.log_nonneg hr0)
      _ ≤ |C| * r ((A.chart j).symm y) :=
        mul_le_mul_of_nonneg_left (Real.log_le_self (by linarith)) (abs_nonneg C)

end GlobalTheory.Mean4O
