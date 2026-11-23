import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.QRHaar
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.LintegralGaussTri
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.ChartWR
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.VolUSetMeasurable

noncomputable section

open Finset Matrix MeasureTheory Filter Topology

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

theorem volU_density (μ : Measure (UNgrp N)) [μ.IsHaarMeasure] [IsProbabilityMeasure μ] (η : ℝ) (hη : 0 < η) :
    ∃ δ > 0, ∀ B : Set (UCo N), MeasurableSet B → (∀ x ∈ B, ‖x‖ < δ) →
      μ {k : UNgrp N | ∃ x ∈ B, toM k = NormedSpace.exp (skMat x)} ≤ ENNReal.ofReal ((1 + η) / volU N) * volume B ∧
        ENNReal.ofReal ((1 - η) / volU N) * volume B ≤ μ {k : UNgrp N | ∃ x ∈ B, toM k = NormedSpace.exp (skMat x)} := by
  obtain ⟨C, -, hC⟩ := qr_lintegral μ
  have hCV : C = volU N := qr_const μ C hC
  subst hCV
  have hV := volU_pos' N
  obtain ⟨ε, hε0, hε1, hkey⟩ : ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ (1 - ε) * (1 + η) = 1 + ε :=
    ⟨η / (2 + η), by positivity, by rw [div_lt_one (by linarith)]; linarith,
      by field_simp; ring⟩
  obtain ⟨δ1, hδ1, hchart⟩ := chartWR_vol (N := N) ε hε0
  obtain ⟨δ2, hδ2, hinj⟩ := volU_exp_injOn (N := N)
  obtain ⟨ρw, hρw, hw⟩ := Metric.continuousAt_iff.1
    (volU_continuous_qrWt (N := N)).continuousAt ε hε0
  obtain ⟨ρ, hρ0, hρ1, hρ2, hρ3⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ δ1 ∧ ρ ≤ ρw ∧ ρ ≤ 1 :=
    ⟨min δ1 (min ρw 1), lt_min hδ1 (lt_min hρw one_pos), min_le_left _ _,
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun B hB hBs => ?_⟩
  show μ (volUSet B) ≤ _ ∧ _ ≤ μ (volUSet B)
  have hBsub : B ⊆ Metric.ball 0 δ2 := fun x hx =>
    mem_ball_zero_iff.2 ((hBs x hx).trans_le (min_le_right _ _))
  have hA : MeasurableSet (volUSet B) := volUSet_measurable hinj hB hBsub
  have hE'pos : Metric.ball (volUOne N) ρ ⊆ triPos N := volU_ball_sub_triPos hρ3
  set S := qrMap '' (volUSet B ×ˢ Metric.ball (volUOne N) ρ) with hSdef
  have hS : MeasurableSet S := qrMap_measurableSet_image _ (hA.prod Metric.isOpen_ball.measurableSet)
    (fun p hp => ⟨Set.mem_univ _, hE'pos hp.2⟩)
  set I := ∫⁻ t in Metric.ball (volUOne N) ρ, ENNReal.ofReal (qrWt t) with hIdef
  have hmem : ∀ k (t : TriCo N), t ∈ triPos N →
      (qrMap (k, t) ∈ S ↔ k ∈ volUSet B ∧ t ∈ Metric.ball (volUOne N) ρ) := by
    intro k t ht
    constructor
    · rintro ⟨⟨k', t'⟩, ⟨hk', ht'⟩, heq⟩
      have := qrMap_injOn ⟨Set.mem_univ _, hE'pos ht'⟩ ⟨Set.mem_univ _, ht⟩ heq
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj this
      exact ⟨hk', ht'⟩
    · rintro ⟨hk, ht'⟩
      exact ⟨(k, t), ⟨hk, ht'⟩, rfl⟩
  have hin : ∀ k, (∫⁻ t in triPos N, S.indicator 1 (qrMap (k, t)) * ENNReal.ofReal (qrWt t)) =
      (volUSet B).indicator (fun _ => I) k := by
    intro k
    by_cases hk : k ∈ volUSet B
    · rw [Set.indicator_of_mem hk, hIdef,
        ← Set.inter_eq_left.2 hE'pos, ← setLIntegral_indicator Metric.isOpen_ball.measurableSet]
      refine setLIntegral_congr_fun volU_measurableSet_triPos (fun t ht => ?_)
      by_cases ht' : t ∈ Metric.ball (volUOne N) ρ
      · rw [Set.indicator_of_mem ((hmem k t ht).2 ⟨hk, ht'⟩), Set.indicator_of_mem ht', Pi.one_apply,
          one_mul]
      · rw [Set.indicator_of_notMem (fun h => ht' ((hmem k t ht).1 h).2), Set.indicator_of_notMem ht',
          zero_mul]
    · rw [Set.indicator_of_notMem hk]
      rw [setLIntegral_congr_fun volU_measurableSet_triPos (g := fun _ => 0) (fun t ht => by
        simp only
        rw [Set.indicator_of_notMem (fun h => hk ((hmem k t ht).1 h).1), zero_mul])]
      simp
  have hSeq : volume S = ENNReal.ofReal (volU N) * (I * μ (volUSet B)) := by
    have h := hC (S.indicator 1) (measurable_one.indicator hS)
    rw [lintegral_indicator_one hS] at h
    rw [h, lintegral_congr hin, lintegral_indicator_const hA]
  have : Measure.IsAddHaarMeasure (volume : Measure (TriCo N)) := by
    show Measure.IsAddHaarMeasure ((volume : Measure (Fin N → ℝ)).prod
      (volume : Measure ({ab : Fin N × Fin N // ab.1 < ab.2} → ℂ)))
    exact Measure.prod.instIsAddHaarMeasure _ _
  have : Measure.IsAddHaarMeasure (volume : Measure (UCo N)) := by
    show Measure.IsAddHaarMeasure ((volume : Measure (Fin N → ℝ)).prod
      (volume : Measure ({ab : Fin N × Fin N // ab.2 < ab.1} → ℂ)))
    exact Measure.prod.instIsAddHaarMeasure _ _
  have hE : volume (Metric.ball (volUOne N) ρ) = volume (Metric.ball (0 : TriCo N) ρ) :=
    Measure.addHaar_ball_center _ _ _
  have hIlo : ENNReal.ofReal (1 - ε) * volume (Metric.ball (0 : TriCo N) ρ) ≤ I := by
    rw [← hE, ← setLIntegral_const]
    refine setLIntegral_mono' Metric.isOpen_ball.measurableSet (fun t ht => ENNReal.ofReal_le_ofReal ?_)
    have := hw (lt_of_lt_of_le (Metric.mem_ball.1 ht) hρ2)
    rw [volU_qrWt_one, Real.dist_eq] at this
    linarith [neg_abs_le (qrWt t - 1)]
  have hIhi : I ≤ ENNReal.ofReal (1 + ε) * volume (Metric.ball (0 : TriCo N) ρ) := by
    rw [← hE, ← setLIntegral_const]
    refine setLIntegral_mono' Metric.isOpen_ball.measurableSet (fun t ht => ENNReal.ofReal_le_ofReal ?_)
    have := hw (lt_of_lt_of_le (Metric.mem_ball.1 ht) hρ2)
    rw [volU_qrWt_one, Real.dist_eq] at this
    linarith [le_abs_self (qrWt t - 1)]
  obtain ⟨hup, hlo⟩ := hchart B (Metric.ball 0 ρ) hB Metric.isOpen_ball.measurableSet
    (fun x hx => (hBs x hx).trans_le (min_le_left _ _))
    (fun t ht => (mem_ball_zero_iff.1 ht).trans_le hρ1)
  rw [volU_image_eq, ← hSdef, hSeq] at hup hlo

  have hEpos : 0 < volume (Metric.ball (0 : TriCo N) ρ) := Metric.measure_ball_pos _ _ hρ0
  have hEfin : volume (Metric.ball (0 : TriCo N) ρ) ≠ ⊤ := measure_ball_lt_top.ne
  have hBfin : volume B ≠ ⊤ := ((measure_mono hBsub).trans_lt measure_ball_lt_top).ne
  have hAfin : μ (volUSet B) ≠ ⊤ := measure_ne_top μ _
  have hIfin : I ≠ ⊤ := (hIhi.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hEfin.lt_top)).ne
  set a := (μ (volUSet B)).toReal
  set b := (volume B).toReal
  set e := (volume (Metric.ball (0 : TriCo N) ρ)).toReal
  set i := I.toReal
  have ha' : μ (volUSet B) = ENNReal.ofReal a := (ENNReal.ofReal_toReal hAfin).symm
  have hb' : volume B = ENNReal.ofReal b := (ENNReal.ofReal_toReal hBfin).symm
  have he' : volume (Metric.ball (0 : TriCo N) ρ) = ENNReal.ofReal e := (ENNReal.ofReal_toReal hEfin).symm
  have hi' : I = ENNReal.ofReal i := (ENNReal.ofReal_toReal hIfin).symm
  have he0 : 0 < e := ENNReal.toReal_pos hEpos.ne' hEfin
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have hb0 : 0 ≤ b := ENNReal.toReal_nonneg
  have hi0 : 0 ≤ i := ENNReal.toReal_nonneg
  rw [ha', hb', he', hi'] at hup hlo
  rw [he', hi'] at hIlo hIhi
  rw [← ENNReal.ofReal_mul hi0, ← ENNReal.ofReal_mul hV.le] at hup hlo
  rw [← ENNReal.ofReal_mul hb0, ← ENNReal.ofReal_mul (by linarith)] at hup
  rw [← ENNReal.ofReal_mul hb0, ← ENNReal.ofReal_mul' (by positivity)] at hlo
  rw [← ENNReal.ofReal_mul (by linarith)] at hIhi
  rw [← ENNReal.ofReal_mul' he0.le] at hIlo
  have h1 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hup
  have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hlo
  have h3 := (ENNReal.ofReal_le_ofReal_iff hi0).1 hIlo
  have h4 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hIhi
  obtain ⟨r1, r2⟩ := volU_real hV he0 ha0 hb0 hε0 hε1 hη hkey h1 h2 h3 h4
  rw [ha', hb']
  constructor
  · rw [← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal r1
  · rw [← ENNReal.ofReal_mul' hb0]
    exact ENNReal.ofReal_le_ofReal r2

end ReciprocityTheory.ChartRestriction.DS
