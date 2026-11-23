import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SGaugeDensPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SGaugeCdPfB

open MeasureTheory Filter Topology Set Function
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.S.Gauge

variable {n : ℕ}

theorem setForm0 (ε : Fin n → Bool) : ∃ c : ℝ, 0 < c ∧ ∃ s : ℝ, 0 < s ∧ Set.InjOn (expC ε) (Metric.ball 0 s) ∧
    ∀ T : Set (EL ε), T ⊆ Metric.ball 0 s → MeasurableSet T →
      Formalism.REAL.muG ε (expC ε '' T) = ENNReal.ofReal c * ∫⁻ t in T, jd ε t := by
  have hN := chartNhd ε
  obtain ⟨s₀, hs₀, hL⟩ := locInvOf ε (transC ε) (jacInv ε)
  obtain ⟨ρ₀, hρ₀, hinj⟩ := injOn_thetaExp ε
  have hs : 0 < min s₀ ρ₀ := lt_min hs₀ hρ₀
  set s := min s₀ ρ₀ with hsdef
  have hLs : LocInv ε s := hL s hs (min_le_left _ _)
  have hinjs : Set.InjOn (expC ε) (Metric.ball 0 s) := by
    intro a ha b hb e
    apply hinj (Metric.ball_subset_ball (min_le_right _ _) ha) (Metric.ball_subset_ball (min_le_right _ _) hb)
    have := congrArg uMat e
    rw [uMat_expC, uMat_expC] at this
    exact Matrix.of.injective this
  have hVo : IsOpen (interior (expC ε '' Metric.ball (0 : EL ε) s)) := isOpen_interior
  have hVW : interior (expC ε '' Metric.ball (0 : EL ε) s) ⊆ expC ε '' Metric.ball (0 : EL ε) s := interior_subset
  have hV1 : (1 : Formalism.REAL.UJ ε) ∈ interior (expC ε '' Metric.ball (0 : EL ε) s) :=
    mem_interior_iff_mem_nhds.2 (hN s hs)
  set V := interior (expC ε '' Metric.ball (0 : EL ε) s) with hVdef
  have hcovN : ∀ x : Formalism.REAL.UJ ε, (fun h => x * h) '' V ∈ 𝓝 x := fun x =>
    ((isOpenMap_mul_left x) V hVo).mem_nhds ⟨1, hV1, mul_one x⟩
  have hOm' : ∀ y : Formalism.REAL.UJ ε, MeasurableSet ((fun h => y * h) '' V) := fun y =>
    ((isOpenMap_mul_left y) V hVo).measurableSet
  obtain ⟨S, hSc, hSU⟩ := TopologicalSpace.countable_cover_nhds hcovN
  have hSne : S.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have : (1 : Formalism.REAL.UJ ε) ∈ ⋃ x ∈ S, (fun h => x * h) '' V := by rw [hSU]; trivial
    rw [h] at this; simp at this
  obtain ⟨xs, hxs⟩ := hSc.exists_eq_range hSne
  let O : ℕ → Set (Formalism.REAL.UJ ε) := fun i => (fun h => xs i * h) '' V
  have hOU : ⋃ i, O i = univ := by rw [← hSU, hxs, Set.biUnion_range]
  have hD : ∀ i, MeasurableSet (disjointed O i) := MeasurableSet.disjointed fun i => hOm' (xs i)
  have hdisj : Pairwise (Disjoint on disjointed O) := disjoint_disjointed O
  have hcov : ⋃ i, disjointed O i = univ := by rw [iUnion_disjointed, hOU]
  have hDV : ∀ i, disjointed O i ⊆ (fun h => xs i * h) '' V := fun i => disjointed_subset O i
  haveI : Measure.IsMulLeftInvariant (nuG ε s xs (disjointed O)) := ⟨fun g => nuG_leftInv hLs hVW hD hdisj hcov hDV g⟩
  haveI : IsLocallyFiniteMeasure (nuG ε s xs (disjointed O)) := ⟨fun y => ⟨(fun h => y * h) '' V, hcovN y, by
      rw [nuG_eq hLs hVW hD hdisj hcov hDV y (hOm' y) (image_mono hVW)]
      calc (lamM ε s).map (fun h => y * h) ((fun h => y * h) '' V) ≤ (lamM ε s).map (fun h => y * h) univ :=
            measure_mono (subset_univ _)
        _ = lamM ε s univ := by rw [Measure.map_apply (measurable_const_mul y) MeasurableSet.univ, preimage_univ]
        _ < ∞ := lamM_univ_lt_top ε s⟩⟩
  haveI : Measure.IsHaarMeasure (Formalism.REAL.muG ε) := by unfold Formalism.REAL.muG; infer_instance
  have hνμ := Measure.isMulLeftInvariant_eq_smul (nuG ε s xs (disjointed O)) (Formalism.REAL.muG ε)
  set κ := Measure.haarScalarFactor (nuG ε s xs (disjointed O)) (Formalism.REAL.muG ε) with hκdef
  have hformT : ∀ T : Set (EL ε), T ⊆ Metric.ball 0 s → MeasurableSet T →
      nuG ε s xs (disjointed O) (expC ε '' T) = ∫⁻ t in T, jd ε t := by
    intro T hsub hT
    have hm : MeasurableSet (expC ε '' T) :=
      hT.image_of_continuousOn_injOn (continuous_expCG ε).continuousOn (hinjs.mono hsub)
    have hsubW : expC ε '' T ⊆ (fun h => (1 : Formalism.REAL.UJ ε) * h) '' (expC ε '' Metric.ball 0 s) := by
      simp only [one_mul, image_id']; exact image_mono hsub
    rw [nuG_eq hLs hVW hD hdisj hcov hDV 1 hm hsubW]
    have hmap : (lamM ε s).map (fun h => (1 : Formalism.REAL.UJ ε) * h) = lamM ε s := by
      simp only [one_mul]; exact Measure.map_id
    rw [hmap, lamM_applyG ε s hm]
    rw [show expC ε ⁻¹' (expC ε '' T) ∩ Metric.ball 0 s = T from ?_]
    ext t
    constructor
    · rintro ⟨⟨t', ht', e⟩, ht⟩
      rw [← hinjs (hsub ht') ht e]; exact ht'
    · intro ht; exact ⟨⟨t, ht, rfl⟩, hsub ht⟩
  obtain ⟨η, hη, hcont⟩ := Metric.continuousAt_iff.1 ((continuous_chartJac_thetaExp ε).continuousAt (x := 0)) (1 / 2)
    (by norm_num)
  have hρ1 : 0 < min s η := lt_min hs hη
  have hpos : ∫⁻ t in Metric.ball (0 : EL ε) (min s η), jd ε t ≠ 0 := by
    have hle : ENNReal.ofReal (1 / 2) * volume (Metric.ball (0 : EL ε) (min s η)) ≤
        ∫⁻ t in Metric.ball (0 : EL ε) (min s η), jd ε t := by
      rw [← setLIntegral_const]
      refine lintegral_mono_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_ball] with t ht
      have := hcont (lt_of_lt_of_le ht (min_le_right _ _))
      rw [chartJac_thetaExp_zero, Real.dist_eq] at this
      exact ENNReal.ofReal_le_ofReal (by linarith [(abs_lt.1 this).1])
    refine (lt_of_lt_of_le ?_ hle).ne'
    exact ENNReal.mul_pos (by simp) (Metric.measure_ball_pos _ _ hρ1).ne'
  have hκ : κ ≠ 0 := by
    intro h0
    apply hpos
    rw [← hformT _ (Metric.ball_subset_ball (min_le_left _ _)) measurableSet_ball, hνμ, h0, zero_smul]
    rfl
  have hκpos : (0 : ℝ) < (κ : ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hκ)
  refine ⟨((κ : ℝ))⁻¹, inv_pos.2 hκpos, s, hs, hinjs, fun T hsub hT => ?_⟩
  have h1 := hformT T hsub hT
  rw [hνμ] at h1
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h1
  rw [← h1, ← mul_assoc, ENNReal.ofReal_inv_of_pos hκpos, ENNReal.ofReal_coe_nnreal,
    ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.2 hκ) ENNReal.coe_ne_top, one_mul]

theorem setForm (ε : Fin n → Bool) : ∃ s : ℝ, 0 < s ∧ Set.InjOn (expC ε) (Metric.ball 0 s) ∧
    ∀ T : Set (EL ε), T ⊆ Metric.ball 0 s → MeasurableSet T →
      Formalism.REAL.muG ε (expC ε '' T) = ENNReal.ofReal (gaugeU ε) * ∫⁻ t in T, jd ε t := by
  obtain ⟨c, hc, s, hs, hinj, hT⟩ := setForm0 ε
  have hb : ∀ ρ : ℝ, 0 < ρ → ρ ≤ s →
      Formalism.REAL.muG ε (expSet ε (Metric.ball (0 : gLie ε) ρ)) = ENNReal.ofReal c * ∫⁻ t in Metric.ball (0 : EL ε) ρ, jd ε t := by
    intro ρ _ hρs
    rw [expSet_ball_eq_image]
    exact hT _ (Metric.ball_subset_ball hρs) measurableSet_ball
  have he := gaugeU_eq (tendsto_ratioAt_of_ball hc hs hb)
  rw [he]
  exact ⟨s, hs, hinj, hT⟩

theorem norm_le_two_l1_norm (ε : Fin n → Bool) (t : EL ε) : ‖t‖ ≤ 2 * ∑ i, ∑ j, ‖linT ε t i j‖ := by
  set x : EuclideanSpace ℝ (Fin n × Fin n × Bool) := ((obG ε).repr.symm t).1 with hx
  have h1 : ‖t‖ = ‖x‖ := by rw [hx]; exact ((obG ε).repr.symm.norm_map t).symm
  have h2 : ‖x‖ ≤ ∑ p, ‖x p‖ := by
    rw [EuclideanSpace.norm_eq]
    calc √(∑ p, ‖x p‖ ^ 2) ≤ √((∑ p, ‖x p‖) ^ 2) :=
          Real.sqrt_le_sqrt (Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _))
      _ = ∑ p, ‖x p‖ := Real.sqrt_sq (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have h3 : ∑ p, ‖x p‖ ≤ 2 * ∑ i, ∑ j, ‖linT ε t i j‖ := by
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_le_sum (fun j _ => ?_)
    rw [Fintype.sum_bool, linT_apply]
    have hre : ‖x (i, j, false)‖ ≤ ‖unrealify x i j‖ := by
      rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm (unrealify x i j)
    have him : ‖x (i, j, true)‖ ≤ ‖unrealify x i j‖ := by
      rw [Real.norm_eq_abs]; exact Complex.abs_im_le_norm (unrealify x i j)
    linarith
  linarith

theorem l1B_subset_ball_two_mul (ε : Fin n → Bool) (r : ℝ) : l1B ε r ⊆ Metric.ball 0 (2 * r) := fun t ht => by
  rw [mem_ball_zero_iff]
  have h := norm_le_two_l1_norm ε t
  have ht' : ∑ i, ∑ j, ‖linT ε t i j‖ < r := ht
  linarith

theorem continuous_matrixEntryAbsSum (ε : Fin n → Bool) : Continuous (fun t : EL ε => ∑ i, ∑ j, ‖linT ε t i j‖) := by
  refine continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ => ?_))
  exact ((continuous_apply j).comp ((continuous_apply i).comp (linT ε).continuous)).norm

theorem isOpen_l1B (ε : Fin n → Bool) (r : ℝ) : IsOpen (l1B ε r) := isOpen_lt (continuous_matrixEntryAbsSum ε) continuous_const

theorem zero_mem_l1B (ε : Fin n → Bool) {r : ℝ} (hr : 0 < r) : (0 : EL ε) ∈ l1B ε r := by
  show ∑ i, ∑ j, ‖linT ε 0 i j‖ < r
  simp [map_zero, hr]

theorem l1BallDensity_signs (ε : Fin n → Bool) : L1BallDensity ε := by
  obtain ⟨s, hs, _, hT⟩ := setForm ε
  have hJ : Tendsto (fun r : ℝ => (∫⁻ t in l1B ε r, jd ε t) / volume (l1B ε r)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    rw [ENNReal.tendsto_nhds ENNReal.one_ne_top]
    intro e he
    obtain ⟨δ0, _, h0δ, hδe⟩ := ENNReal.lt_iff_exists_real_btwn.1 he
    have hδ0p : 0 < δ0 := ENNReal.ofReal_pos.1 h0δ
    have hδp : 0 < min δ0 (1 / 2) := lt_min hδ0p (by norm_num)
    have hδ1 : min δ0 (1 / 2) ≤ 1 / 2 := min_le_right _ _
    have hδe' : ENNReal.ofReal (min δ0 (1 / 2)) ≤ e := (ENNReal.ofReal_le_ofReal (min_le_left _ _)).trans hδe.le
    obtain ⟨η, hη, hcont⟩ := Metric.continuousAt_iff.1 ((continuous_chartJac_thetaExp ε).continuousAt (x := 0))
      (min δ0 (1 / 2)) hδp
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < η / 2 by linarith)] with r hr
    have hsub : l1B ε r ⊆ Metric.ball 0 η :=
      (l1B_subset_ball_two_mul ε r).trans (Metric.ball_subset_ball (by linarith [hr.2]))
    have hbd : ∀ t ∈ l1B ε r, |chartJac (thetaExp ε) t - 1| < min δ0 (1 / 2) := by
      intro t ht
      have h := hcont (show dist t 0 < η from hsub ht)
      rwa [chartJac_thetaExp_zero, Real.dist_eq] at h
    have hm : MeasurableSet (l1B ε r) := (isOpen_l1B ε r).measurableSet
    have hV0 : volume (l1B ε r) ≠ 0 := ((isOpen_l1B ε r).measure_pos volume ⟨0, zero_mem_l1B ε hr.1⟩).ne'
    have hVt : volume (l1B ε r) ≠ ∞ := ((measure_mono (l1B_subset_ball_two_mul ε r)).trans_lt measure_ball_lt_top).ne
    have hup : ∫⁻ t in l1B ε r, jd ε t ≤ ENNReal.ofReal (1 + min δ0 (1 / 2)) * volume (l1B ε r) := by
      rw [← setLIntegral_const]
      refine lintegral_mono_ae ?_
      filter_upwards [ae_restrict_mem hm] with t ht
      exact ENNReal.ofReal_le_ofReal (by linarith [(abs_lt.1 (hbd t ht)).2])
    have hlo : ENNReal.ofReal (1 - min δ0 (1 / 2)) * volume (l1B ε r) ≤ ∫⁻ t in l1B ε r, jd ε t := by
      rw [← setLIntegral_const]
      refine lintegral_mono_ae ?_
      filter_upwards [ae_restrict_mem hm] with t ht
      exact ENNReal.ofReal_le_ofReal (by linarith [(abs_lt.1 (hbd t ht)).1])
    constructor
    · rw [ENNReal.le_div_iff_mul_le (Or.inl hV0) (Or.inl hVt)]
      refine le_trans ?_ hlo
      gcongr
      rw [ENNReal.ofReal_sub 1 hδp.le, ENNReal.ofReal_one]
      exact tsub_le_tsub_left hδe' 1
    · rw [ENNReal.div_le_iff hV0 hVt]
      refine hup.trans ?_
      gcongr
      rw [ENNReal.ofReal_add zero_le_one hδp.le, ENNReal.ofReal_one]
      gcongr
  have hlim : Tendsto (fun r : ℝ => ENNReal.ofReal (gaugeU ε) * ((∫⁻ t in l1B ε r, jd ε t) / volume (l1B ε r)))
      (𝓝[>] (0 : ℝ)) (𝓝 (ENNReal.ofReal (gaugeU ε) * 1)) :=
    ENNReal.Tendsto.const_mul hJ (Or.inr ENNReal.ofReal_ne_top)
  rw [mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < s / 2 by linarith)] with r hr
  rw [hT _ ((l1B_subset_ball_two_mul ε r).trans (Metric.ball_subset_ball (by linarith [hr.2]))) (isOpen_l1B ε r).measurableSet,
    mul_div_assoc]

theorem l1BallMeasurable_signs (ε : Fin n → Bool) : L1BallMeasurable ε := by
  obtain ⟨s, hs, hinj, -⟩ := setForm ε
  refine ⟨s / 2, by linarith, fun r hr => ?_⟩
  have hsub : l1B ε r ⊆ Metric.ball 0 s := (l1B_subset_ball_two_mul ε r).trans (Metric.ball_subset_ball (by linarith))
  exact (isOpen_l1B ε r).measurableSet.image_of_continuousOn_injOn (continuous_expCG ε).continuousOn (hinj.mono hsub)

end Formalism.MainNotions.S.Gauge
