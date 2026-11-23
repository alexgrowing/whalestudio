import Mathlib
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SignedLogMeans
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.AbsoluteLogMeanBounds

noncomputable section

namespace GlobalTheory.Theta0MeanCompare

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

theorem setting_iff (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ)
    (t : (M →ₐ[ℚ] ℂ) → ℂ) : SignedLogMeans.HidaSetting D cc δ M t ↔ AbsoluteLogMeanBounds.HidaSetting D cc δ M t := Iff.rfl

theorem bound_eq (D : D7) : SignedLogMeans.bound D = AbsoluteLogMeanBounds.kronBound D := rfl

theorem meanLog_eq (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (Λ : AddSubgroup ℂ)
    (t : (M →ₐ[ℚ] ℂ) → ℂ) : SignedLogMeans.meanLog M Λ t = AbsoluteLogMeanBounds.meanLog Λ M t := by
  unfold SignedLogMeans.meanLog AbsoluteLogMeanBounds.meanLog AbsoluteLogMeanBounds.mean SignedLogMeans.conjNormSq AbsoluteLogMeanBounds.th0NormSq
  congr!

theorem meanPosLog_eq (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (Λ : AddSubgroup ℂ)
    (t : (M →ₐ[ℚ] ℂ) → ℂ) : SignedLogMeans.meanPosLog M Λ t = AbsoluteLogMeanBounds.meanLogPos Λ M t := by
  unfold SignedLogMeans.meanPosLog AbsoluteLogMeanBounds.meanLogPos AbsoluteLogMeanBounds.mean SignedLogMeans.conjNormSq AbsoluteLogMeanBounds.th0NormSq
  simp only [max_comm (0 : ℝ)]
  try congr!

theorem one_le_d (D : D7) : (1 : ℝ) ≤ D.host.d := by
  have h := D.host.qd_big.2
  exact_mod_cast (by omega : 1 ≤ D.host.d)

theorem two_sqrt_le_rd (D : D7) : 2 * Real.sqrt D.host.d ≤ D.host.rdE := by
  refine le_trans ?_ (factRd D.R D.host).1
  have he : (2 : ℝ) ≤ D.R.e := by exact_mod_cast D.host.two_le_e
  have h1 : (2 : ℝ) ^ (-(D.R.e : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ ((D.R.e : ℝ) + 1 - (2 : ℝ) ^ (-(D.R.e : ℝ))) := by
    calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  exact mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _)

theorem one_le_sqrt_d (D : D7) : 1 ≤ Real.sqrt D.host.d := Real.one_le_sqrt.mpr (one_le_d D)

theorem log_v_nonneg (D : D7) : 0 ≤ Real.log D.host.v := by
  apply Real.log_nonneg
  have h1 := two_sqrt_le_rd D
  have h2 := one_le_sqrt_d D
  unfold Host.v
  linarith

theorem kronBound_le (D : D7) {L : ℝ} (h : Real.log D.host.rdE + |logDerivativeAtOne D| ≤ 2 * L) :
    AbsoluteLogMeanBounds.kronBound D ≤ L := by
  have h1 := two_sqrt_le_rd D
  have h2 := one_le_sqrt_d D
  have h3 : Real.log (Real.sqrt D.host.d) ≤ Real.log D.host.rdE :=
    Real.log_le_log (by linarith) (by linarith)
  have h4 := Real.one_half_lt_eulerMascheroniConstant
  have h5 := le_abs_self (logDerivativeAtOne D)
  unfold AbsoluteLogMeanBounds.kronBound
  linarith

theorem signedMean_iff :
    ((∀ D : D7, SignedLogMeans.SignedMean D) ∧ ∀ D : D7, SignedLogMeans.MeanLeL D) ↔ AbsoluteLogMeanBounds.SignedMean := by
  constructor
  · rintro ⟨h1, h2⟩ D cc δ M _ t hS
    rw [← meanLog_eq]
    exact ⟨h1 D cc δ M t hS, fun L hL => ⟨kronBound_le D hL, h2 D cc δ M t hS L hL⟩⟩
  · intro h
    refine ⟨fun D cc δ M _ t hS => ?_, fun D cc δ M _ t hS L hL => ?_⟩
    · rw [meanLog_eq]; exact (h D cc δ M t hS).1
    · rw [meanLog_eq]; exact ((h D cc δ M t hS).2 L hL).2

theorem absoluteMean_iff :
    ((∃ C : ℝ, 0 ≤ C ∧ ∀ D : D7, SignedLogMeans.MeanLeC C D) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ D : D7, SignedLogMeans.PosMeanLeC C D) ↔ AbsoluteLogMeanBounds.AbsoluteMean := by
  constructor
  · rintro ⟨⟨C₁, hC₁, h1⟩, C₂, hC₂, h2⟩
    refine ⟨C₁ + C₂ + 1, by linarith, fun D cc δ M _ t hS L hL => ?_⟩
    have hL0 : 0 ≤ L := by
      have := log_v_nonneg D
      have := abs_nonneg (logDerivativeAtOne D)
      linarith
    have a1 := h1 D cc δ M t hS L hL
    have a2 := h2 D cc δ M t hS L hL
    rw [← meanLog_eq, ← meanPosLog_eq]
    have := mul_nonneg hC₁ hL0
    have := mul_nonneg hC₂ hL0
    constructor <;> nlinarith
  · rintro ⟨C, hC, h⟩
    refine ⟨⟨C, hC.le, fun D cc δ M _ t hS L hL => ?_⟩, C, hC.le, fun D cc δ M _ t hS L hL => ?_⟩
    · rw [meanLog_eq]; exact (h D cc δ M t hS L hL).1
    · rw [meanPosLog_eq]; exact (h D cc δ M t hS L hL).2

def ExplicitPosMean : Prop :=
  ∃ C : ℝ, ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ)
    [FiniteDimensional ℚ M] (t : (M →ₐ[ℚ] ℂ) → ℂ), AbsoluteLogMeanBounds.HidaSetting D cc δ M t →
    AbsoluteLogMeanBounds.meanLogPos (lamOf D cc δ) M t ≤
      AbsoluteLogMeanBounds.kronBound D + (1 / 4) * Real.log (D.host.d : ℝ) + C

theorem explicitPosMean_of_positivePart (h : AbsoluteLogMeanBounds.PositivePart) : ExplicitPosMean := by
  obtain ⟨C, h⟩ := h
  exact ⟨C, fun D cc δ M _ t hS => (h D cc δ M t hS).2⟩

theorem posMean_iff : (∃ C : ℝ, 0 ≤ C ∧ ∀ D : D7, SignedLogMeans.PosMean C D) ↔ ExplicitPosMean := by
  constructor
  · rintro ⟨C, -, h⟩
    refine ⟨C, fun D cc δ M _ t hS => ?_⟩
    rw [← meanPosLog_eq]
    exact h D cc δ M t hS
  · rintro ⟨C, h⟩
    refine ⟨max C 0, le_max_right _ _, fun D cc δ M _ t hS => ?_⟩
    have a := h D cc δ M t hS
    have := le_max_left C 0
    rw [meanPosLog_eq, bound_eq]
    linarith

theorem core_iff :
    (SignedLogMeans.Theta0SignedMean ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ D : D7, SignedLogMeans.PosMeanLeC C D) ↔ AbsoluteLogMeanBounds.ThetaNullMean := by
  unfold SignedLogMeans.Theta0SignedMean AbsoluteLogMeanBounds.ThetaNullMean
  rw [← signedMean_iff, ← absoluteMean_iff]
  tauto

theorem theta0Mean_iff : SignedLogMeans.Theta0Mean ↔ AbsoluteLogMeanBounds.ThetaNullMean ∧ ExplicitPosMean := by
  unfold SignedLogMeans.Theta0Mean SignedLogMeans.Theta0PosMean
  rw [← core_iff, ← posMean_iff]
  tauto

theorem th0Mean_of_theta0Mean (h : SignedLogMeans.Theta0Mean) : AbsoluteLogMeanBounds.ThetaNullMean := (theta0Mean_iff.mp h).1

theorem theta0Mean_of_th0Mean (h : AbsoluteLogMeanBounds.ThetaNullMean) (hp : AbsoluteLogMeanBounds.PositivePart) : SignedLogMeans.Theta0Mean :=
  theta0Mean_iff.mpr ⟨h, explicitPosMean_of_positivePart hp⟩

end GlobalTheory.Theta0MeanCompare
