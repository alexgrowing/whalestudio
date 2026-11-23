import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun MeasureTheory Topology
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem schwartzBruhat_matrix_lintegral_sq_ne_zero_ne_top : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {a d : ℕ}
    (Φ : Matrix (Fin a) (Fin d) k → ℂ), Φ ∈ SB (Matrix (Fin a) (Fin d) k) → Φ ≠ 0 →
    ∀ ν : @Measure (Matrix (Fin a) (Fin d) k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
      ∫⁻ Y, ‖Φ Y‖ₑ ^ 2 ∂ν ≠ 0 ∧ ∫⁻ Y, ‖Φ Y‖ₑ ^ 2 ∂ν ≠ ⊤ := by
  intro k _ _ _ _ a d Φ hΦ h0 ν hν
  letI : MeasurableSpace (Matrix (Fin a) (Fin d) k) := borel _
  haveI : BorelSpace (Matrix (Fin a) (Fin d) k) := ⟨rfl⟩
  obtain ⟨hlc, hcs⟩ : IsLocallyConstant Φ ∧ HasCompactSupport Φ := hΦ
  have hc : Continuous Φ := hlc.continuous
  have hcont : Continuous fun Y => ‖Φ Y‖ₑ ^ 2 :=
    (ENNReal.continuous_pow 2).comp hc.enorm
  constructor
  · intro h
    rw [lintegral_eq_zero_iff hcont.measurable] at h
    have h' := (Continuous.ae_eq_iff_eq ν hcont continuous_zero).1 h
    apply h0
    funext Y
    have := congrFun h' Y
    simpa using this
  · obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hcs
    have hle : ∫⁻ Y, ‖Φ Y‖ₑ ^ 2 ∂ν ≤
        ∫⁻ Y, (tsupport Φ).indicator (fun _ => ENNReal.ofReal C ^ 2) Y ∂ν := by
      refine lintegral_mono fun Y => ?_
      by_cases hY : Y ∈ tsupport Φ
      · rw [Set.indicator_of_mem hY]
        gcongr
        rw [← ofReal_norm_eq_enorm]
        exact ENNReal.ofReal_le_ofReal (hC Y)
      · simp [image_eq_zero_of_notMem_tsupport hY]
    refine ne_top_of_le_ne_top ?_ hle
    rw [lintegral_indicator_const (isClosed_tsupport Φ).measurableSet]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      (IsCompact.measure_lt_top hcs).ne

end GlobalTheory
