import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory Set
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential mInt MIntegrable locDens ChartPartition)

noncomputable section

namespace TailLogOfMass

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X} {Yo : Set X}
  {th : LocPot X} {u : Fin D → X → ℝ}

theorem potForm_contDiffAt (hYo : IsOpen Yo) (hth : IsPotential A th)
    (hu : ∀ i, A.SmoothOn Yo (u i)) (i : Fin D) (x : X) (k : Fin A.n) {y : Fin D → ℂ}
    (hy : y ∈ (A.chart k).target) (hyYo : (A.chart k).symm y ∈ Yo)
    (hyU : (A.chart k).symm y ∈ th.U x) :
    ContDiffAt ℝ 2 ((potForm th (u i)).φ x ∘ (A.chart k).symm) y := by
  have h1 := ReciprocityTheory.AnForm.M.pot_contDiffAt_two hth x k hy hyU
  have ho : IsOpen ((A.chart k).target ∩ (A.chart k).symm ⁻¹' Yo) :=
    (A.chart k).isOpen_inter_preimage_symm hYo
  have h2 : ContDiffAt ℝ 2 (u i ∘ (A.chart k).symm) y :=
    ((hu i k).contDiffAt (ho.mem_nhds ⟨hy, hyYo⟩)).of_le (WithTop.coe_le_coe.2 le_top)
  exact h1.add h2

theorem locDens_nonneg_on (hYo : IsOpen Yo) (hth : IsPotential A th)
    (hu : ∀ i, A.SmoothOn Yo (u i)) (hnn : ∀ i, FormNonneg A Yo (potForm th (u i)))
    (j : Fin A.n) {y : Fin D → ℂ} (hy : y ∈ (A.chart j).target) (hyYo : (A.chart j).symm y ∈ Yo) :
    0 ≤ locDens A (fun i => potForm th (u i)) j y :=
  ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ y fun i =>
    ReciprocityTheory.AnForm.M.hessC_posSemidef_of_levi _ y
      (potForm_contDiffAt hYo hth hu i _ j hy hyYo (th.mem_U _))
      (fun w => hnn i _ j y ⟨hy, hyYo, (potForm th (u i)).mem_U _⟩ w)

theorem locDens_chart_on (hYo : IsOpen Yo) (hth : IsPotential A th)
    (hu : ∀ i, A.SmoothOn Yo (u i)) (j k : Fin A.n) {y : Fin D → ℂ} (hy : y ∈ (A.chart j).target)
    (hyk : (A.chart j).symm y ∈ (A.chart k).source) (hyYo : (A.chart j).symm y ∈ Yo) :
    locDens A (fun i => potForm th (u i)) j y =
      locDens A (fun i => potForm th (u i)) k (A.chart k ((A.chart j).symm y)) *
        Complex.normSq (ReciprocityTheory.AnForm.A.jacC (A.chart k ∘ (A.chart j).symm) y).det := by
  set Φ : Fin D → LocPot X := fun i => potForm th (u i) with hΦ
  have hτ : AnalyticAt ℂ (A.chart k ∘ (A.chart j).symm) y := A.holo j k y ⟨hy, hyk⟩
  have hsk : (A.chart k).symm (A.chart k ((A.chart j).symm y)) = (A.chart j).symm y :=
    (A.chart k).left_inv hyk
  have htk : A.chart k ((A.chart j).symm y) ∈ (A.chart k).target := (A.chart k).map_source hyk
  have hL : locDens A Φ k (A.chart k ((A.chart j).symm y)) =
      ReciprocityTheory.AnForm.maDens (fun i y' => (Φ i).φ ((A.chart j).symm y) ((A.chart k).symm y'))
        (A.chart k ((A.chart j).symm y)) := by
    simp only [locDens, hsk]
  have hsm : ∀ i, ContDiffAt ℝ 2 (fun y' => (Φ i).φ ((A.chart j).symm y) ((A.chart k).symm y'))
      ((A.chart k ∘ (A.chart j).symm) y) := fun i =>
    potForm_contDiffAt hYo hth hu i _ k htk
      (show (A.chart k).symm (A.chart k ((A.chart j).symm y)) ∈ Yo by rw [hsk]; exact hyYo)
      (show (A.chart k).symm (A.chart k ((A.chart j).symm y)) ∈ th.U ((A.chart j).symm y) by
        rw [hsk]; exact th.mem_U _)
  have hcomp := ReciprocityTheory.AnForm.A.maDens_comp
    (fun i y' => (Φ i).φ ((A.chart j).symm y) ((A.chart k).symm y'))
    (A.chart k ∘ (A.chart j).symm) y hτ hsm
  have key : locDens A Φ j y = ReciprocityTheory.AnForm.maDens (fun i =>
      (fun y' => (Φ i).φ ((A.chart j).symm y) ((A.chart k).symm y')) ∘
        (A.chart k ∘ (A.chart j).symm)) y := by
    unfold locDens
    apply ReciprocityTheory.AnForm.M.maDens_congr_hessC
    intro i
    apply ReciprocityTheory.AnForm.M.hessCGerm
    have hWo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source) :=
      (A.chart j).isOpen_inter_preimage_symm (A.chart k).open_source
    filter_upwards [hWo.mem_nhds (show y ∈ (A.chart j).target ∩
      (A.chart j).symm ⁻¹' (A.chart k).source from ⟨hy, hyk⟩)] with w hw
    simp only [Function.comp_apply]
    rw [(A.chart k).left_inv hw.2]
  rw [hL, key]
  exact hcomp

theorem weight_nonneg (hYo : IsOpen Yo) (hth : IsPotential A th)
    (hu : ∀ i, A.SmoothOn Yo (u i)) (hnn : ∀ i, FormNonneg A Yo (potForm th (u i)))
    (P : ChartPartition A) (h : X → ℝ) (h0 : ∀ x, 0 ≤ h x) (hoff : ∀ x, x ∉ Yo → h x = 0)
    (i : Fin A.n) {z : Fin D → ℂ} (hz : z ∈ (A.chart i).target) :
    0 ≤ P.χ i ((A.chart i).symm z) * h ((A.chart i).symm z) * locDens A (fun i => potForm th (u i)) i z := by
  by_cases hzY : (A.chart i).symm z ∈ Yo
  · exact mul_nonneg (mul_nonneg (P.nonneg i _) (h0 _)) (locDens_nonneg_on hYo hth hu hnn i hz hzY)
  · rw [hoff _ hzY]; simp

theorem lintegral_target_le (hYo : IsOpen Yo) (hth : IsPotential A th)
    (hu : ∀ i, A.SmoothOn Yo (u i)) (hnn : ∀ i, FormNonneg A Yo (potForm th (u i)))
    (P : ChartPartition A) (h : X → ℝ) (h0 : ∀ x, 0 ≤ h x) (hoff : ∀ x, x ∉ Yo → h x = 0)
    (j : Fin A.n) (hm : AEMeasurable (fun y => h ((A.chart j).symm y) * locDens A (fun i => potForm th (u i)) j y)
      (volume.restrict (A.chart j).target)) :
    ∫⁻ y in (A.chart j).target, ENNReal.ofReal (h ((A.chart j).symm y) * locDens A (fun i => potForm th (u i)) j y) ≤
      ∑ i, ∫⁻ z in (A.chart i).target, ENNReal.ofReal (P.χ i ((A.chart i).symm z) *
        h ((A.chart i).symm z) * locDens A (fun i => potForm th (u i)) i z) := by
  have hT : MeasurableSet (A.chart j).target := (A.chart j).open_target.measurableSet
  have hχ : ∀ i, ContinuousOn (fun y => P.χ i ((A.chart j).symm y)) (A.chart j).target := by
    intro i
    have := (P.smooth i j).continuousOn
    rw [Set.preimage_univ, Set.inter_univ] at this
    exact this
  have hsplit : ∀ y ∈ (A.chart j).target,
      ENNReal.ofReal (h ((A.chart j).symm y) * locDens A (fun i => potForm th (u i)) j y) =
        ∑ i, ENNReal.ofReal (P.χ i ((A.chart j).symm y) *
          (h ((A.chart j).symm y) * locDens A (fun i => potForm th (u i)) j y)) := by
    intro y hy
    by_cases hyY : (A.chart j).symm y ∈ Yo
    · have ha : 0 ≤ h ((A.chart j).symm y) * locDens A (fun i => potForm th (u i)) j y :=
        mul_nonneg (h0 _) (locDens_nonneg_on hYo hth hu hnn j hy hyY)
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (P.nonneg i _) ha),
        ← Finset.sum_mul, P.sum_eq_one, one_mul]
    · simp [hoff _ hyY]
  rw [setLIntegral_congr_fun hT hsplit, lintegral_finsetSum' (f := fun i y => ENNReal.ofReal
    (P.χ i ((A.chart j).symm y) * (h ((A.chart j).symm y) * locDens A (fun i => potForm th (u i)) j y))) _ (fun i _ =>
    ENNReal.measurable_ofReal.comp_aemeasurable (((hχ i).aemeasurable hT).mul hm))]
  refine Finset.sum_le_sum fun i _ => ?_
  have hU : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart i).source) :=
    (A.chart j).isOpen_inter_preimage_symm (A.chart i).open_source
  have hτ : AnalyticOnNhd ℂ (A.chart i ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart i).source) := A.holo j i
  have hinj : Set.InjOn (A.chart i ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart i).source) := by
    intro a ha b hb hab
    exact (A.chart j).symm.injOn ha.1 hb.1 ((A.chart i).injOn ha.2 hb.2 hab)
  have himg : (A.chart i ∘ (A.chart j).symm) ''
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart i).source) ⊆ (A.chart i).target := by
    rintro _ ⟨z, hz, rfl⟩; exact (A.chart i).map_source hz.2
  calc ∫⁻ y in (A.chart j).target, ENNReal.ofReal (P.χ i ((A.chart j).symm y) *
          (h ((A.chart j).symm y) * locDens A (fun i => potForm th (u i)) j y))
        = ∫⁻ y in (A.chart j).target,
          ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart i).source).indicator
            (fun y => ENNReal.ofReal (P.χ i ((A.chart j).symm y) *
              (h ((A.chart j).symm y) * locDens A (fun i => potForm th (u i)) j y))) y := by
          refine setLIntegral_congr_fun hT fun y hy => ?_
          by_cases hyU : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart i).source
          · rw [indicator_of_mem hyU]
          · rw [indicator_of_notMem hyU]
            have h1 : (A.chart j).symm y ∉ (A.chart i).source := fun h' => hyU ⟨hy, h'⟩
            have h2 : (A.chart j).symm y ∉ tsupport (P.χ i) := fun h' =>
              h1 (P.tsupport_subset i h')
            simp [image_eq_zero_of_notMem_tsupport h2]
      _ ≤ ∫⁻ y, ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart i).source).indicator
            (fun y => ENNReal.ofReal (P.χ i ((A.chart j).symm y) *
              (h ((A.chart j).symm y) * locDens A (fun i => potForm th (u i)) j y))) y := setLIntegral_le_lintegral _ _
      _ = ∫⁻ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart i).source,
            ENNReal.ofReal (P.χ i ((A.chart j).symm y) *
              (h ((A.chart j).symm y) * locDens A (fun i => potForm th (u i)) j y)) := lintegral_indicator hU.measurableSet _
      _ = ∫⁻ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart i).source,
            ENNReal.ofReal (Complex.normSq
              (ReciprocityTheory.AnForm.A.jacC (A.chart i ∘ (A.chart j).symm) y).det) *
            (fun z => ENNReal.ofReal (P.χ i ((A.chart i).symm z) *
              h ((A.chart i).symm z) * locDens A (fun i => potForm th (u i)) i z)) ((A.chart i ∘ (A.chart j).symm) y) := by
          refine setLIntegral_congr_fun hU.measurableSet fun y hy => ?_
          have hs : (A.chart i).symm (A.chart i ((A.chart j).symm y)) = (A.chart j).symm y :=
            (A.chart i).left_inv hy.2
          show ENNReal.ofReal (P.χ i ((A.chart j).symm y) *
              (h ((A.chart j).symm y) * locDens A (fun i => potForm th (u i)) j y)) =
            ENNReal.ofReal (Complex.normSq
              (ReciprocityTheory.AnForm.A.jacC (A.chart i ∘ (A.chart j).symm) y).det) *
            ENNReal.ofReal (P.χ i ((A.chart i).symm (A.chart i ((A.chart j).symm y))) *
              h ((A.chart i).symm (A.chart i ((A.chart j).symm y))) *
              locDens A (fun i => potForm th (u i)) i (A.chart i ((A.chart j).symm y)))
          rw [hs, ← ENNReal.ofReal_mul (Complex.normSq_nonneg _)]
          by_cases hyY : (A.chart j).symm y ∈ Yo
          · rw [locDens_chart_on hYo hth hu j i hy.1 hy.2 hyY]
            congr 1
            ring
          · simp [hoff _ hyY]
      _ = ∫⁻ z in (A.chart i ∘ (A.chart j).symm) ''
            ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart i).source),
            ENNReal.ofReal (P.χ i ((A.chart i).symm z) * h ((A.chart i).symm z) *
              locDens A (fun i => potForm th (u i)) i z) :=
          (ReciprocityTheory.AnForm.A.lintegral_image_eq_lintegral_normSq_det_mul _ _ hU hτ hinj
            (fun z => ENNReal.ofReal (P.χ i ((A.chart i).symm z) * h ((A.chart i).symm z) *
              locDens A (fun i => potForm th (u i)) i z))).symm
      _ ≤ ∫⁻ z in (A.chart i).target, ENNReal.ofReal (P.χ i ((A.chart i).symm z) *
            h ((A.chart i).symm z) * locDens A (fun i => potForm th (u i)) i z) := lintegral_mono_set himg

theorem mInt_nonneg_of (hYo : IsOpen Yo) (hth : IsPotential A th)
    (hu : ∀ i, A.SmoothOn Yo (u i)) (hnn : ∀ i, FormNonneg A Yo (potForm th (u i)))
    (h : X → ℝ) (h0 : ∀ x, 0 ≤ h x) (hoff : ∀ x, x ∉ Yo → h x = 0) :
    0 ≤ mInt A (fun i => potForm th (u i)) h := by
  unfold mInt
  split_ifs with hP
  · exact Finset.sum_nonneg fun i _ => setIntegral_nonneg (A.chart i).open_target.measurableSet
      fun z hz => weight_nonneg hYo hth hu hnn _ h h0 hoff i hz
  · exact le_rfl

theorem sum_lintegral_eq_mInt [CompactSpace X] [T2Space X] (hYo : IsOpen Yo)
    (hth : IsPotential A th) (hu : ∀ i, A.SmoothOn Yo (u i))
    (hnn : ∀ i, FormNonneg A Yo (potForm th (u i))) (h : X → ℝ) (h0 : ∀ x, 0 ≤ h x)
    (hoff : ∀ x, x ∉ Yo → h x = 0) (hI : MIntegrable A (fun i => potForm th (u i)) h) :
    ∑ i, ∫⁻ z in (A.chart i).target,
      ENNReal.ofReal ((ReciprocityTheory.AnForm.M.existsPartition A).some.χ i ((A.chart i).symm z) *
        h ((A.chart i).symm z) * locDens A (fun i => potForm th (u i)) i z) = ENNReal.ofReal (mInt A (fun i => potForm th (u i)) h) := by
  rw [mInt, dif_pos (ReciprocityTheory.AnForm.M.existsPartition A)]
  unfold ReciprocityTheory.AnForm.M.integralWith
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => setIntegral_nonneg
    (A.chart i).open_target.measurableSet fun z hz => weight_nonneg hYo hth hu hnn _ h h0 hoff i hz)]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (ofReal_integral_eq_lintegral_ofReal
    (ReciprocityTheory.AnForm.M.integrableOn_weight A _ _ h hI i)
    (ae_restrict_of_forall_mem (A.chart i).open_target.measurableSet
      fun z hz => weight_nonneg hYo hth hu hnn _ h h0 hoff i hz)).symm

end TailLogOfMass

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
