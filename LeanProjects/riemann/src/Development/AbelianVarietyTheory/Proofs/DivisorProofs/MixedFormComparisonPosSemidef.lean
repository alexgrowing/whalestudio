import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparableHermitianFormsDetBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvexCombinationMetricSandwich
open scoped ComplexOrder Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GradedNorm

open Matrix GlobalTheory.LieMet

theorem mix_comparable_of_le {n : ℕ} {B B₀ : Matrix (Fin n) (Fin n) ℂ} {s r R κ C : ℝ} (hB : B.PosDef)
    (hB₀ : B₀.PosDef) (hr : 1 ≤ r) (hrR : r ≤ Real.sqrt R) (hR : 2 ≤ R) (hC : 0 ≤ C) (hκ : 2 * C + 2 < κ)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hs' : 1 - s ≤ (r / R) ^ κ) (hle : (((r ^ C : ℝ) : ℂ) • B - B₀).PosSemidef) :
    ((((1 - R⁻¹)⁻¹ : ℝ) : ℂ) • B - mix s B₀ B).PosSemidef ∧
      ((((1 - R⁻¹)⁻¹ : ℝ) : ℂ) • mix s B₀ B - B).PosSemidef := by
  obtain ⟨h1, h2⟩ := GlobalTheory.interp_metric_close n B B₀ s r R κ C hB hB₀.posSemidef hr hrR (by linarith) hC hκ
    (sub_nonneg.2 hs.2) hs' hle
  have hmix : mix s B₀ B = ((s : ℝ) : ℂ) • B + (((1 - s : ℝ)) : ℂ) • B₀ := add_comm _ _
  rw [← hmix] at h1 h2
  have hR0 : 0 < R := by linarith
  have hq : 0 < 1 - R⁻¹ := by
    have : R⁻¹ ≤ 1 / 2 := by rw [inv_eq_one_div]; exact div_le_div_of_nonneg_left zero_le_one two_pos hR
    linarith
  set m : ℝ := (1 - R⁻¹)⁻¹ with hm
  have hm1 : m * (1 - R⁻¹) = 1 := inv_mul_cancel₀ hq.ne'
  have hm2 : 0 ≤ m - (1 + R⁻¹) := by
    have key : (1 + R⁻¹) * (1 - R⁻¹) ≤ 1 := by nlinarith [sq_nonneg R⁻¹]
    have e : m - (1 + R⁻¹) = m * (1 - (1 + R⁻¹) * (1 - R⁻¹)) := by linear_combination (1 + R⁻¹) * hm1
    rw [e]
    exact mul_nonneg (by positivity) (sub_nonneg.2 key)
  constructor
  · have e : (m : ℂ) • B - mix s B₀ B = ((m - (1 + R⁻¹) : ℝ) : ℂ) • B + ((((1 + R⁻¹ : ℝ)) : ℂ) • B - mix s B₀ B) := by
      rw [Complex.ofReal_sub, sub_smul]; abel
    rw [e]
    exact (hB.posSemidef.smul (Complex.zero_le_real.2 hm2)).add h1
  · have e : (m : ℂ) • mix s B₀ B - B = (m : ℂ) • (mix s B₀ B - (((1 - R⁻¹ : ℝ)) : ℂ) • B) := by
      rw [smul_sub, smul_smul, ← Complex.ofReal_mul, hm1, Complex.ofReal_one, one_smul]
    rw [e]
    exact h2.smul (Complex.zero_le_real.2 (by positivity))

theorem transpose_smul_sub {n : ℕ} (a : ℂ) (X Y : Matrix (Fin n) (Fin n) ℂ) : (a • X - Y)ᵀ = a • Xᵀ - Yᵀ := by
  rw [transpose_sub, transpose_smul]

theorem interp_comparable : ∀ (n : ℕ) (B B₀ : Matrix (Fin n) (Fin n) ℂ) (s r R κ C : ℝ), B.PosDef → B₀.PosDef → 1 ≤ r →
    r ≤ Real.sqrt R → 2 ≤ R → 0 ≤ C → 2 * C + 2 < κ → s ∈ Set.Icc (0 : ℝ) 1 → 1 - s ≤ (r / R) ^ κ →
    (((r ^ C : ℝ) : ℂ) • B₀ - B).PosSemidef → (((r ^ C : ℝ) : ℂ) • B - B₀).PosSemidef →
    ((((1 - R⁻¹)⁻¹ : ℝ) : ℂ) • B - GlobalTheory.GradedNorm.mix s B₀ B).PosSemidef ∧
      ((((1 - R⁻¹)⁻¹ : ℝ) : ℂ) • GlobalTheory.GradedNorm.mix s B₀ B - B).PosSemidef ∧
      ((((1 - R⁻¹)⁻¹ : ℝ) : ℂ) • B - GlobalTheory.GradedNorm.mixDual s B₀ B).PosSemidef ∧
      ((((1 - R⁻¹)⁻¹ : ℝ) : ℂ) • GlobalTheory.GradedNorm.mixDual s B₀ B - B).PosSemidef := by
  intro n B B₀ s r R κ C hB hB₀ hr hrR hR hC hκ hs hs' hge hle
  obtain ⟨a1, a2⟩ := mix_comparable_of_le hB hB₀ hr hrR hR hC hκ hs hs' hle
  refine ⟨a1, a2, ?_⟩
  have hrC : 1 ≤ r ^ C := Real.one_le_rpow hr hC
  obtain ⟨-, d2, -⟩ := GlobalTheory.CompMetric.comparable_metrics n B B₀ (r ^ C) hrC hB hB₀ hge hle
  have hd : (((r ^ C : ℝ) : ℂ) • dualGram B - dualGram B₀).PosSemidef := by
    have := d2.transpose
    rwa [transpose_smul_sub] at this
  have hB' := dualGram_posDef hB
  have hB₀' := dualGram_posDef hB₀
  obtain ⟨b1, b2⟩ := mix_comparable_of_le hB' hB₀' hr hrR hR hC hκ hs hs' hd
  have hR0 : 0 < R := by linarith
  have hq : 0 < 1 - R⁻¹ := by
    have : R⁻¹ ≤ 1 / 2 := by rw [inv_eq_one_div]; exact div_le_div_of_nonneg_left zero_le_one two_pos hR
    linarith
  have hq1 : 1 - R⁻¹ ≤ 1 := by have : 0 < R⁻¹ := inv_pos.2 hR0; linarith
  have hm : 1 ≤ (1 - R⁻¹)⁻¹ := one_le_inv₀ hq |>.2 hq1
  obtain ⟨c1, c2, -⟩ := GlobalTheory.CompMetric.comparable_metrics n (mix s (dualGram B₀) (dualGram B)) (dualGram B) _ hm
    (mix_posDef hs hB₀' hB') hB' b1 b2
  have eB : (dualGram B)⁻¹ᵀ = B := dualGram_dualGram ((isUnit_iff_isUnit_det _).1 hB.isUnit)
  have eM : (mix s (dualGram B₀) (dualGram B))⁻¹ᵀ = mixDual s B₀ B := rfl
  refine ⟨?_, ?_⟩
  · have := c1.transpose
    rwa [transpose_smul_sub, eB, eM] at this
  · have := c2.transpose
    rwa [transpose_smul_sub, eB, eM] at this

end GlobalTheory.GradedNorm
