import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLimitOfChart
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalBasis

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.GaugeWhole

private theorem pos_of_isGauge' {n : ℕ} {ε : Fin n → Bool} {c : ℝ} (h : IsGauge ε c) : 0 < c := by
  have h' : Filter.Tendsto
      (fun r : ℝ => c * (Formalism.REAL.muG ε {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r}).toReal / r ^ (n ^ 2))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal) := h
  have hpos : 0 < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne
  by_contra hc
  push_neg at hc
  have hle : ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      c * (Formalism.REAL.muG ε {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r}).toReal / r ^ (n ^ 2) ≤ 0 := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hc ENNReal.toReal_nonneg)
      (pow_nonneg (le_of_lt hr) _)
  have := le_of_tendsto h' hle
  linarith

theorem isGaugeSub_univ {n : ℕ} {ε : Fin n → Bool} {c : ℝ} (h : IsGauge ε c) :
    0 < c ∧ IsGaugeSub (Set.univ : Set (Formalism.REAL.UJ ε)) (n ^ 2) (ENNReal.ofReal c • Formalism.REAL.muG ε) := by
  have hc := pos_of_isGauge' h
  have h' : Filter.Tendsto
      (fun r : ℝ => c * (Formalism.REAL.muG ε {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r}).toReal / r ^ (n ^ 2))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal) := h
  have hpos : 0 < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne
  have hfin : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1) ≠ ⊤ := measure_ball_lt_top.ne
  refine ⟨hc, ?_⟩
  unfold IsGaugeSub
  refine ⟨by simp, fun s _ => ?_, ?_⟩
  · rw [Measure.map_smul, map_mul_left_eq_self]
  · rw [← ENNReal.ofReal_toReal hfin]
    refine (ENNReal.tendsto_ofReal h').congr' ?_
    filter_upwards [h'.eventually (lt_mem_nhds hpos), self_mem_nhdsWithin] with r hr hr0
    have hr0' : (0 : ℝ) < r := hr0
    have hμ : Formalism.REAL.muG ε {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} ≠ ⊤ := by
      intro htop
      rw [htop] at hr
      simp at hr
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.ofReal_div_of_pos (pow_pos hr0' _),
      ENNReal.ofReal_mul hc.le, ENNReal.ofReal_toReal hμ]

theorem gauge_whole : ∀ (n : ℕ) (ε : Fin n → Bool), (∀ c : ℝ, IsGauge ε c → 0 < c ∧ IsGaugeSub (Set.univ : Set (Formalism.REAL.UJ ε)) (n ^ 2) (ENNReal.ofReal c • Formalism.REAL.muG ε)) ∧ ∃ (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (E : Fin (n ^ 2) → Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) ∧ (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) ∧ (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) ∧ (Set.univ : Set (Formalism.REAL.UJ ε)) = {g | uMat g - 1 ∈ A} := by
  intro n ε
  refine ⟨fun c hc => isGaugeSub_univ hc, ?_⟩
  obtain ⟨E, hE, horth, hexp⟩ := GlobalTheory.LieONB.exists_orthonormal_basis n ε
  refine ⟨⊤, E, fun _ _ _ _ => Submodule.mem_top, horth, fun X => ?_, ?_⟩
  · constructor
    · rintro ⟨-, hX⟩
      rw [hexp X hX]
      refine Submodule.sum_mem _ fun i _ => ?_
      have hs : ((((X * (E i)ᴴ).trace).re : ℝ) : ℂ) • E i = (((X * (E i)ᴴ).trace).re : ℝ) • E i := by
        ext a b
        simp [Complex.real_smul]
      rw [hs]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · intro hX
      refine ⟨Submodule.mem_top, ?_⟩
      have hle : Submodule.span ℝ (Set.range E) ≤ GlobalTheory.GaugeConst.lieJ ε := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact GlobalTheory.GaugeConst.mem_lieJ.mpr (hE i).1
      exact GlobalTheory.GaugeConst.mem_lieJ.mp (hle hX)
  · ext g
    simp

end GlobalTheory.GaugeWhole
