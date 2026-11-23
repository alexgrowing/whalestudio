import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.RingKrullDimQuotBotOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial MeasureTheory Measure

noncomputable section

theorem finrank_real_euclideanSpace_complex (d : ℕ) :
    Module.finrank ℝ (EuclideanSpace ℂ (Fin d)) = 2 * d := by
  rw [((EuclideanSpace.equiv (Fin d) ℂ).toLinearEquiv.restrictScalars ℝ).finrank_eq]
  simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]

instance isAddHaarMeasure_hausdorffMeasure_euclideanSpace_complex (d : ℕ) :
    (μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d))).IsAddHaarMeasure := by
  have := isAddHaarMeasure_hausdorffMeasure (E := EuclideanSpace ℂ (Fin d))
  rwa [finrank_real_euclideanSpace_complex] at this

theorem map_hausdorffMeasure_euclideanSpace_apply (d : ℕ) (s : Set (Fin d → ℂ)) :
    (μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d))).map
        (EuclideanSpace.equiv (Fin d) ℂ) s =
      μH[((2 * d : ℕ) : ℝ)] (EuclideanSpace.equiv (Fin d) ℂ ⁻¹' s) :=
  (EuclideanSpace.equiv (Fin d) ℂ).toHomeomorph.toMeasurableEquiv.map_apply s

theorem nnreal_mul_ofReal_le (c : NNReal) (C η α : ℝ) :
    (c : ENNReal) * ENNReal.ofReal (C * η ^ α) ≤ ENNReal.ofReal (((c : ℝ) + 1) * C * η ^ α) := by
  have h1 : (c : ENNReal) ≤ ENNReal.ofReal ((c : ℝ) + 1) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  rw [mul_assoc, ENNReal.ofReal_mul (p := (c : ℝ) + 1) (by positivity)]
  exact mul_le_mul_of_nonneg_right h1 (zero_le)

theorem PolySublevel.equiv :
    GroundTheory.Heights₂.Heights.PolySublevel.Statement ↔ PolySublevel.Statement := by
  constructor
  · intro h d Q hQ R hR
    set e := EuclideanSpace.equiv (Fin d) ℂ
    set K := ‖(e : EuclideanSpace ℂ (Fin d) →L[ℂ] (Fin d → ℂ))‖
    have hK : 0 ≤ K := norm_nonneg _
    obtain ⟨C, α, hC, hα, hb⟩ := h d Q hQ ((K + 1) * R) (by positivity)
    have hc := isAddLeftInvariant_eq_smul
      ((μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d))).map e)
      (volume : Measure (Fin d → ℂ))
    set c := addHaarScalarFactor
      ((μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d))).map e)
      (volume : Measure (Fin d → ℂ))
    refine ⟨((c : ℝ) + 1) * C, α, by positivity, hα, fun η hη hη1 => ?_⟩
    calc _ ≤ μH[((2 * d : ℕ) : ℝ)]
          (e ⁻¹' {x : Fin d → ℂ | x ∈ Metric.ball 0 ((K + 1) * R) ∧ ‖eval x Q‖ ≤ η}) := by
          apply measure_mono
          rintro x ⟨hx, hxη⟩
          refine ⟨?_, hxη⟩
          rw [mem_ball_zero_iff] at hx ⊢
          calc ‖e x‖ = ‖(e : EuclideanSpace ℂ (Fin d) →L[ℂ] (Fin d → ℂ)) x‖ := rfl
            _ ≤ K * ‖x‖ := ContinuousLinearMap.le_opNorm _ x
            _ ≤ K * R := by gcongr
            _ < (K + 1) * R := by nlinarith
      _ = ((μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d))).map e)
          {x : Fin d → ℂ | x ∈ Metric.ball 0 ((K + 1) * R) ∧ ‖eval x Q‖ ≤ η} :=
          (map_hausdorffMeasure_euclideanSpace_apply d _).symm
      _ = (c : ENNReal) *
          volume {x : Fin d → ℂ | x ∈ Metric.ball 0 ((K + 1) * R) ∧ ‖eval x Q‖ ≤ η} := by
          rw [hc]; rfl
      _ ≤ (c : ENNReal) * ENNReal.ofReal (C * η ^ α) := by gcongr; exact hb η hη hη1
      _ ≤ _ := nnreal_mul_ofReal_le c C η α
  · intro h d Q hQ R hR
    set e := EuclideanSpace.equiv (Fin d) ℂ
    set K := ‖(e.symm : (Fin d → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin d))‖
    have hK : 0 ≤ K := norm_nonneg _
    obtain ⟨C, α, hC, hα, hb⟩ := h d Q hQ ((K + 1) * R) (by positivity)
    have hc := isAddLeftInvariant_eq_smul (volume : Measure (Fin d → ℂ))
      ((μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d))).map e)
    set c := addHaarScalarFactor (volume : Measure (Fin d → ℂ))
      ((μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d))).map e)
    refine ⟨((c : ℝ) + 1) * C, α, by positivity, hα, fun η hη hη1 => ?_⟩
    calc _ = (c : ENNReal) * ((μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d))).map e)
          {x : Fin d → ℂ | x ∈ Metric.ball 0 R ∧ ‖eval x Q‖ ≤ η} := by
          conv_lhs => rw [hc]
          rfl
      _ = (c : ENNReal) * μH[((2 * d : ℕ) : ℝ)]
          (e ⁻¹' {x : Fin d → ℂ | x ∈ Metric.ball 0 R ∧ ‖eval x Q‖ ≤ η}) := by
          rw [map_hausdorffMeasure_euclideanSpace_apply]
      _ ≤ (c : ENNReal) * μH[((2 * d : ℕ) : ℝ)]
          {x : EuclideanSpace ℂ (Fin d) | x ∈ Metric.ball 0 ((K + 1) * R) ∧
            ‖eval (fun i => x i) Q‖ ≤ η} := by
          gcongr
          rintro x ⟨hx, hxη⟩
          refine ⟨?_, hxη⟩
          rw [mem_ball_zero_iff] at hx ⊢
          calc ‖x‖ = ‖(e.symm : (Fin d → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin d)) (e x)‖ := by simp
            _ ≤ K * ‖e x‖ := ContinuousLinearMap.le_opNorm _ _
            _ ≤ K * R := by gcongr
            _ < (K + 1) * R := by nlinarith
      _ ≤ (c : ENNReal) * ENNReal.ofReal (C * η ^ α) := by gcongr; exact hb η hη hη1
      _ ≤ _ := nnreal_mul_ofReal_le c C η α

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
