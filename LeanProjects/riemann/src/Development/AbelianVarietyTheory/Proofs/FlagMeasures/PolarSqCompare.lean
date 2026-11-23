import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PerpendicularEmbedding
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CdScaleIsTrueScale
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousGaussSp
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuadricPointGaugePolarCoordinatesCompareTangentG

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal

namespace GlobalTheory.PolarCompare

theorem abs_qf_le_sum_sq {P Q : ℕ} (z : Sp P Q) : |qf z| ≤ ∑ i, ‖z i‖ ^ 2 := by
  have h1 : 0 ≤ ∑ i : Fin P, ‖z (Sum.inl i)‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have h2 : 0 ≤ ∑ j : Fin Q, ‖z (Sum.inr j)‖ ^ 2 := Finset.sum_nonneg fun j _ => by positivity
  rw [Fintype.sum_sum_type]
  simp only [qf, Complex.normSq_eq_norm_sq]
  rw [abs_le]
  constructor <;> linarith

theorem sq_compare_left {T S N r s : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S) (hN : 0 ≤ N)
    (hr0 : 0 < r) (hr1 : r < 1 / 2) (hr : 3 * r < 1 - s) (h1 : N ≤ T + S)
    (h : T ^ 2 + 2 * S < s * r ^ 2) : N ^ 2 + 2 * S < r ^ 2 := by

  have hr2 : 0 < r ^ 2 := by positivity
  have hs : s < 1 := by linarith
  have hsr : s * r ^ 2 < r ^ 2 := by nlinarith
  have hS2 : 2 * S < r ^ 2 := by nlinarith
  have hT2 : T ^ 2 < r ^ 2 := by nlinarith
  have hTr : T < r := by nlinarith
  have hN2 : N * N ≤ (T + S) * (T + S) := mul_self_le_mul_self hN h1
  have a1 : T * S ≤ r * S := mul_le_mul_of_nonneg_right hTr.le hS
  have a2 : r * (2 * S) ≤ r * r ^ 2 := mul_le_mul_of_nonneg_left hS2.le hr0.le
  have a3 : (2 * S) * (2 * S) ≤ r ^ 2 * r ^ 2 := mul_self_le_mul_self (by linarith) hS2.le
  have a4 : r * r ^ 2 * r ≤ r * r ^ 2 * (1 / 2) :=
    mul_le_mul_of_nonneg_left hr1.le (by positivity)
  have a5 : 3 * r * r ^ 2 < (1 - s) * r ^ 2 := mul_lt_mul_of_pos_right hr hr2
  nlinarith [mul_pos hr0 hr2]

theorem sq_compare_right {T S N E r s : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S) (hN : 0 ≤ N)
    (hr0 : 0 < r) (hr1 : r < 1 / 2) (hr : 11 * r < s - 1) (h1 : E ≤ N + S) (h2 : T ≤ 2 * E)
    (h3 : T ≤ 2 → T - T ^ 3 / 16 ≤ E)
    (h : N ^ 2 + 2 * S < r ^ 2) : T ^ 2 + 2 * S < s * r ^ 2 := by

  have hr2 : 0 < r ^ 2 := by positivity
  have hS2 : 2 * S < r ^ 2 := by nlinarith
  have hNr : N < r := by nlinarith
  have hrr : r ^ 2 < r / 2 := by nlinarith [mul_pos hr0 (sub_pos.mpr hr1)]
  have hT3r : T ≤ 3 * r := by linarith
  have hTE : T - T ^ 3 / 16 ≤ E := h3 (by linarith)
  have hc1 : T * T ≤ 3 * r * (3 * r) := mul_self_le_mul_self hT hT3r
  have hc2 : T * T * T ≤ 3 * r * (3 * r) * (3 * r) := mul_le_mul hc1 hT3r hT (by positivity)
  have hr3 : r ^ 2 * r ≤ r ^ 2 * (1 / 2) := mul_le_mul_of_nonneg_left hr1.le (sq_nonneg r)
  have hb0 : 0 ≤ S + T ^ 3 / 16 := by positivity
  have hb2 : S + T ^ 3 / 16 ≤ 2 * r ^ 2 := by nlinarith
  have hTNb : T ≤ N + (S + T ^ 3 / 16) := by linarith
  have hT2 : T * T ≤ (N + (S + T ^ 3 / 16)) * (N + (S + T ^ 3 / 16)) :=
    mul_self_le_mul_self hT hTNb
  have a1 : N * (S + T ^ 3 / 16) ≤ r * (S + T ^ 3 / 16) :=
    mul_le_mul_of_nonneg_right hNr.le hb0
  have a2 : r * (S + T ^ 3 / 16) ≤ r * (2 * r ^ 2) := mul_le_mul_of_nonneg_left hb2 hr0.le
  have a3 : (S + T ^ 3 / 16) * (S + T ^ 3 / 16) ≤ (2 * r ^ 2) * (2 * r ^ 2) :=
    mul_self_le_mul_self hb0 hb2
  have a4 : r * r ^ 2 * r ≤ r * r ^ 2 * (1 / 2) :=
    mul_le_mul_of_nonneg_left hr1.le (by positivity)
  have a5 : 11 * r * r ^ 2 < (s - 1) * r ^ 2 := mul_lt_mul_of_pos_right hr hr2
  nlinarith [mul_pos hr0 hr2]

theorem polar_sq_compare : ∀ (P Q P' Q' : ℕ) (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (t : ℝ), 1 < t → ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ u : ℝ × Sp P' Q', u.1 ∈ Set.Ioo (-Real.pi) Real.pi → (tanSq u < (t⁻¹ * r) ^ 2 → ptSq e (polarPt e u) < r ^ 2) ∧ (ptSq e (polarPt e u) < r ^ 2 → tanSq u < (t * r) ^ 2) := by
  intro P Q P' Q' e t ht
  have ht0 : 0 < t := by linarith
  have hA : 0 < 1 - t⁻¹ ^ 2 := by
    have h1 : t⁻¹ < 1 := inv_lt_one_of_one_lt₀ ht
    have h2 : 0 < t⁻¹ := inv_pos.mpr ht0
    nlinarith
  have hB : 0 < t ^ 2 - 1 := by nlinarith
  have hc : 0 < min (1 / 2 : ℝ) (min ((1 - t⁻¹ ^ 2) / 3) ((t ^ 2 - 1) / 11)) :=
    lt_min (by norm_num) (lt_min (div_pos hA (by norm_num)) (div_pos hB (by norm_num)))
  filter_upwards [inter_mem_nhdsWithin (Set.Ioi (0 : ℝ)) (Iio_mem_nhds hc)] with r hr
  obtain ⟨hr0, hrc⟩ := hr
  simp only [Set.mem_Ioi, Set.mem_Iio] at hr0 hrc
  have hr1 : r < 1 / 2 := lt_of_lt_of_le hrc (min_le_left _ _)
  have hr2 : 3 * r < 1 - t⁻¹ ^ 2 := by
    have := lt_of_lt_of_le hrc ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hr3 : 11 * r < t ^ 2 - 1 := by
    have := lt_of_lt_of_le hrc ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  rintro ⟨θ, z⟩ hu
  simp only [Set.mem_Ioo] at hu
  have hθ : |θ| ≤ Real.pi := abs_le.mpr ⟨hu.1.le, hu.2.le⟩

  have hq : |sg (e none) * qf z| ≤ ∑ i, ‖z i‖ ^ 2 := by
    rw [abs_mul]
    rcases sg_eq (e none) with h | h <;> rw [h] <;> simpa using abs_qf_le_sum_sq z
  have hρ1 := (abs_sqrt_sub_one_le (sg (e none) * qf z)).trans hq
  have hw1 : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  have hpt : ptSq e (polarPt e (θ, z)) =
      ‖(Real.sqrt (1 - sg (e none) * qf z) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) - 1‖ ^ 2 +
        2 * ∑ i, ‖z i‖ ^ 2 := by
    simp only [ptSq, polarPt_none, polarPt_some]
  have htan : tanSq (θ, z) = |θ| ^ 2 + 2 * ∑ i, ‖z i‖ ^ 2 := by
    simp only [tanSq, sq_abs]
  obtain ⟨hb1, hb2, hb3⟩ := exp_bounds θ hθ
  rw [hpt, htan]
  generalize Real.sqrt (1 - sg (e none) * qf z) = ρ at hρ1 ⊢
  generalize Complex.exp ((θ : ℂ) * Complex.I) = w at hw1 hb1 hb2 hb3 ⊢
  generalize ∑ i, ‖z i‖ ^ 2 = S at hρ1 ⊢
  have hS0 : 0 ≤ S := (abs_nonneg _).trans hρ1
  have hdiff : ‖(ρ : ℂ) * w - w‖ = |ρ - 1| := by
    have : (ρ : ℂ) * w - w = ((ρ - 1 : ℝ) : ℂ) * w := by push_cast; ring
    rw [this, norm_mul, hw1, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hNE : ‖(ρ : ℂ) * w - 1‖ ≤ |θ| + S := by
    have := norm_sub_le_norm_sub_add_norm_sub ((ρ : ℂ) * w) w 1
    rw [hdiff] at this
    linarith
  have hEN : ‖w - 1‖ ≤ ‖(ρ : ℂ) * w - 1‖ + S := by
    have := norm_sub_le_norm_sub_add_norm_sub w ((ρ : ℂ) * w) 1
    rw [norm_sub_rev w ((ρ : ℂ) * w), hdiff] at this
    linarith
  constructor
  · intro h
    rw [mul_pow] at h
    exact sq_compare_left (abs_nonneg θ) hS0 (norm_nonneg _) hr0 hr1 hr2 hNE h
  · intro h
    rw [mul_pow]
    exact sq_compare_right (abs_nonneg θ) hS0 (norm_nonneg _) hr0 hr1 hr3 hEN hb2 hb3 h

end GlobalTheory.PolarCompare
