import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

theorem muG_preimage_conj {n : ℕ} (ε : Fin n → Bool) (u : Formalism.REAL.UJ ε) (B : Set (Formalism.REAL.UJ ε)) :
    Formalism.REAL.muG ε ((fun g => u⁻¹ * g * u) ⁻¹' B) = Formalism.REAL.muG ε B := by
  haveI : (Formalism.REAL.muG ε).IsMulRightInvariant := ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular n ε g⟩
  haveI : (Formalism.REAL.muG ε).IsHaarMeasure := by unfold Formalism.REAL.muG; infer_instance
  have : (fun g => u⁻¹ * g * u) ⁻¹' B = (fun g => u⁻¹ * g) ⁻¹' ((fun g => g * u) ⁻¹' B) := rfl
  rw [this, measure_preimage_mul, measure_preimage_mul_right]

theorem gauge_map_of_iso : ∀ (n n' : ℕ) (ε : Fin n → Bool) (ε' : Fin n' → Bool), n = n' → ∀ (T : Formalism.REAL.UJ ε ≃ₜ* Formalism.REAL.UJ ε') (u : Formalism.REAL.UJ ε), (∀ g, Formalism.REAL.hs (uMat (T (u * g * u⁻¹)) - 1) = Formalism.REAL.hs (uMat g - 1)) → ∀ c c' : ℝ, IsGauge ε c → IsGauge ε' c' → (ENNReal.ofReal c • Formalism.REAL.muG ε).map T = ENNReal.ofReal c' • Formalism.REAL.muG ε' := by
  intro n n' ε ε' hn T u hT c c' hc hc'
  subst hn
  haveI : (Formalism.REAL.muG ε).IsHaarMeasure := by unfold Formalism.REAL.muG; infer_instance
  haveI : (Formalism.REAL.muG ε').IsHaarMeasure := by unfold Formalism.REAL.muG; infer_instance
  haveI : ((Formalism.REAL.muG ε).map T).IsHaarMeasure := T.isHaarMeasure_map _
  obtain ⟨a, ha⟩ : ∃ a : NNReal, (Formalism.REAL.muG ε).map T = a • Formalism.REAL.muG ε' :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul _ _⟩
  have hball : ∀ r : ℝ, Formalism.REAL.muG ε {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} =
      a * Formalism.REAL.muG ε' {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} := by
    intro r
    have h1 := congrArg (fun m : Measure (Formalism.REAL.UJ ε') =>
      m {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r}) ha
    have h2 := MeasurableEquiv.map_apply (μ := Formalism.REAL.muG ε) T.toHomeomorph.toMeasurableEquiv
      {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r}
    have h3 : (T : Formalism.REAL.UJ ε → Formalism.REAL.UJ ε') ⁻¹' {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} =
        (fun g => u⁻¹ * g * u) ⁻¹' {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} := by
      ext g
      have := hT (u⁻¹ * g * u)
      rw [show u * (u⁻¹ * g * u) * u⁻¹ = g by group] at this
      simp only [Set.mem_preimage, Set.mem_setOf_eq, this]
    change (Formalism.REAL.muG ε).map T _ = Formalism.REAL.muG ε ((T : Formalism.REAL.UJ ε → Formalism.REAL.UJ ε') ⁻¹' _) at h2
    rw [h3, muG_preimage_conj] at h2
    rw [← h2]
    simpa using h1
  have hω : 0 < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne
  have hca : c' = c * a := by
    have h1 := Filter.Tendsto.const_mul c' hc
    have h2 := Filter.Tendsto.const_mul (c * a) hc'
    have h3 := tendsto_nhds_unique h1 (h2.congr fun r => by
      rw [hball r, ENNReal.toReal_mul, ENNReal.coe_toReal]; ring)
    exact mul_right_cancel₀ hω.ne' h3
  rw [Measure.map_smul, ha, hca, ENNReal.ofReal_mul' a.coe_nonneg, ENNReal.ofReal_coe_nnreal, mul_smul]
  rfl

end GlobalTheory.FlagMeas
