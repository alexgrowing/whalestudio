import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsScaleStable
set_option maxSynthPendingDepth 1

open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace ModelDimension.ConeBallLogGap

theorem logGap_eq_ofReal_of_ne {n : ℕ} (h : HermNorm n) (u : Fin n → ℂ)
    {y : EuclideanSpace ℂ (Fin n)} (hy : y ≠ 0) (hs : ∑ j, u j * h.pointOf y j ≠ 0) :
    logGap h u y = ENNReal.ofReal (Real.log (h.norm u) - fsLog h u (h.pointOf y)) ∧
      0 ≤ Real.log (h.norm u) - fsLog h u (h.pointOf y) := by
  refine ⟨by simp [logGap, hy, hs], ?_⟩
  have hy' : 0 < ‖y‖ := norm_pos_iff.mpr hy
  rw [ConeFsLog.fsLog_pointOf, sub_nonneg]
  exact Real.log_le_log (div_pos (norm_pos_iff.mpr hs) hy')
    ((div_le_iff₀ hy').mpr (ConeFsLog.norm_sum_mul_pointOf_le h u y))

theorem coneBall_logGap_integral (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (u : Fin n → ℂ)
    (hW : IsProjPrime W) (hf : IsChowForm W (e + 1) f) (hu : linForm u ∉ W) :
    ∫⁻ y in coneBall h W, logGap h u y ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) < ⊤ ∧
      (∫⁻ y in coneBall h W, logGap h u y ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ))).toReal =
        Real.log (h.norm u) * ((Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) (coneBall h W)).toReal -
          ∫ y in coneBall h W, fsLog h u (h.pointOf y) ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) := by
  have hfin := ConeBallFinite.full n e h W f hW hf
  have hint := ConeFsLogIntegrable.full n e h W f u hW hf hu
  have hnull := ConeHyperplaneNull.full n e h W f u hW hf hu
  set ν : Measure (EuclideanSpace ℂ (Fin n)) := Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) with hν
  have h0 : ν {0} = 0 := by
    haveI := Measure.nullSingletonClass_hausdorff (X := EuclideanSpace ℂ (Fin n))
      (d := ((2 * (e + 1) : ℕ) : ℝ)) (by positivity)
    exact measure_singleton 0
  haveI : IsFiniteMeasure (ν.restrict (coneBall h W)) := ⟨by simpa using hfin⟩
  have hp : Continuous (fun y : EuclideanSpace ℂ (Fin n) => h.pointOf y) := by
    unfold HermNorm.pointOf; fun_prop
  have hc : Continuous (fun y : EuclideanSpace ℂ (Fin n) => ∑ j, u j * h.pointOf y j) :=
    continuous_finsetSum _ fun j _ => continuous_const.mul ((continuous_apply j).comp hp)
  have hZm : MeasurableSet {y : EuclideanSpace ℂ (Fin n) | ∑ j, u j * h.pointOf y j = 0} :=
    (isClosed_eq hc continuous_const).measurableSet
  have hZ : (ν.restrict (coneBall h W)) {y | ∑ j, u j * h.pointOf y j = 0} = 0 := by
    rw [Measure.restrict_apply hZm, Set.inter_comm]
    exact hnull
  have h0' : ∀ᵐ y ∂(ν.restrict (coneBall h W)), y ∈ ({0} : Set (EuclideanSpace ℂ (Fin n)))ᶜ :=
    ae_mono Measure.restrict_le_self (compl_mem_ae_iff.mpr h0)
  have hgood : ∀ᵐ y ∂(ν.restrict (coneBall h W)),
      logGap h u y = ENNReal.ofReal (Real.log (h.norm u) - fsLog h u (h.pointOf y)) ∧
        0 ≤ Real.log (h.norm u) - fsLog h u (h.pointOf y) := by
    filter_upwards [compl_mem_ae_iff.mpr hZ, h0'] with y hy1 hy2
    exact logGap_eq_ofReal_of_ne h u hy2 hy1
  have hFint : Integrable (fun y => Real.log (h.norm u) - fsLog h u (h.pointOf y))
      (ν.restrict (coneBall h W)) := (integrable_const _).sub hint
  have hlin : ∫⁻ y in coneBall h W, logGap h u y ∂ν =
      ENNReal.ofReal (∫ y in coneBall h W, (Real.log (h.norm u) - fsLog h u (h.pointOf y)) ∂ν) := by
    rw [ofReal_integral_eq_lintegral_ofReal hFint (hgood.mono fun y hy => hy.2)]
    exact lintegral_congr_ae (hgood.mono fun y hy => hy.1)
  have hI : ∫ y in coneBall h W, (Real.log (h.norm u) - fsLog h u (h.pointOf y)) ∂ν =
      Real.log (h.norm u) * (ν (coneBall h W)).toReal -
        ∫ y in coneBall h W, fsLog h u (h.pointOf y) ∂ν := by
    rw [integral_sub (integrable_const _) hint, setIntegral_const, measureReal_def, smul_eq_mul,
      mul_comm]
  refine ⟨by rw [hlin]; exact ENNReal.ofReal_lt_top, ?_⟩
  rw [hlin, ENNReal.toReal_ofReal (integral_nonneg_of_ae (hgood.mono fun y hy => hy.2)), hI]

end ModelDimension.ConeBallLogGap

theorem ModelDimension.integral_coneBall_log_gap_eq : ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
  (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (u : Fin n → ℂ),
  IsProjPrime W → IsChowForm W (e + 1) f → linForm u ∉ W →
    ∫⁻ y in coneBall h W, logGap h u y ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) < ⊤ ∧
      (∫⁻ y in coneBall h W, logGap h u y ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ))).toReal =
        Real.log (h.norm u) * ((Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) (coneBall h W)).toReal -
          ∫ y in coneBall h W, fsLog h u (h.pointOf y) ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) :=
  fun n e h W f u hW hf hu => ModelDimension.ConeBallLogGap.coneBall_logGap_integral n e h W f u hW hf hu
