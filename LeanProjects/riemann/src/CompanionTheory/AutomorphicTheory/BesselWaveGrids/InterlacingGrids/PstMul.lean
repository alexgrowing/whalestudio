import Mathlib
import CompanionTheory.AutomorphicTheory.BesselWaveGrids.InterlacingGrids.PairOKOfInterlace
import CompanionTheory.AutomorphicTheory.BesselWaveGrids.InterlacingGrids.Bracket

namespace GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid

open Finset

theorem bracket_const_le (k r : ℕ) (c b : ℝ) (hc : 0 ≤ c) (hb : 3 ≤ b) (hkb : (k : ℝ) ≤ b)
    (hcb : c + 2 ≤ b) :
    (2 + c) ^ 2 * (k : ℝ) ^ 2 * (3 * b) ^ (2 * r + 3) ≤ b ^ (4 * r + 10) := by
  have hb0 : 0 ≤ b := by linarith
  have h1 : (2 + c) ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have h2 : (k : ℝ) ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg k) hkb 2
  have h3 : (3 * b) ^ (2 * r + 3) ≤ (b * b) ^ (2 * r + 3) :=
    pow_le_pow_left₀ (by linarith) (by nlinarith) _
  calc (2 + c) ^ 2 * (k : ℝ) ^ 2 * (3 * b) ^ (2 * r + 3)
      ≤ b ^ 2 * b ^ 2 * (b * b) ^ (2 * r + 3) := by
        apply mul_le_mul (mul_le_mul h1 h2 (sq_nonneg _) (sq_nonneg _)) h3
          (pow_nonneg (by linarith) _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = b ^ (4 * r + 10) := by ring

theorem pst_mul_le (k r : ℕ) (lam u v : ℕ → ℝ) (e e' : ℕ) (c g b Y : ℝ) (hk : 2 ≤ k) (hc : 0 ≤ c)
    (hg : 1 + c ≤ g) (hb : 3 ≤ b) (hkb : (k : ℝ) ≤ b) (hcb : c + 2 ≤ b) (hY : |Y| ≤ b)
    (hlam : ∀ s, 1 ≤ s → s ≤ k + 2 * r + 1 → |lam s| ≤ b)
    (hgap : ∀ s, 1 ≤ s → s + 1 ≤ k - 1 → lam (s + 1) + g ≤ lam s)
    (hp : PairOK k lam u e (-Y)) (hp' : PairOK k lam v e' (-Y))
    (hden : ∀ i, 1 ≤ i → i ≤ k → 1 ≤ |Y + 1 / 2 + u i|) (hden' : ∀ i, 1 ≤ i → i ≤ k → 1 ≤ |Y + 1 / 2 + v i|) :
    Pst k r lam c Y * Pst k r lam c (Y + 1) ≤
      b ^ (8 * r + 20) * ∏ i ∈ Icc 1 k, (|Y + 1 / 2 + u i| * |Y + 1 / 2 + v i|) := by
  have hP1 := bracket_le k r lam u e c g b Y 0 hk hc hg (Or.inl rfl) (by linarith) hY hlam hgap hp hden
  have hP2 := bracket_le k r lam v e' c g b Y 1 hk hc hg (Or.inr rfl) (by linarith) hY hlam hgap hp' hden'
  simp only [add_zero] at hP1
  have hKc := bracket_const_le k r c b hc hb hkb hcb
  have hKc0 : 0 ≤ (2 + c) ^ 2 * (k : ℝ) ^ 2 * (3 * b) ^ (2 * r + 3) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (pow_nonneg (by linarith) _)
  have hPu : 0 ≤ ∏ i ∈ Icc 1 k, |Y + 1 / 2 + u i| := prod_nonneg fun _ _ => abs_nonneg _
  have hPv : 0 ≤ ∏ i ∈ Icc 1 k, |Y + 1 / 2 + v i| := prod_nonneg fun _ _ => abs_nonneg _
  have hQ : 0 ≤ ∏ s ∈ Icc 1 (k + 2 * r + 1), (|Y + 1 + lam s| + c) :=
    prod_nonneg fun _ _ => add_nonneg (abs_nonneg _) hc
  unfold Pst
  rw [prod_mul_distrib]
  calc (∏ s ∈ Icc 1 (k + 2 * r + 1), (|Y + lam s| + c)) *
        ∏ s ∈ Icc 1 (k + 2 * r + 1), (|Y + 1 + lam s| + c)
      ≤ ((2 + c) ^ 2 * (k : ℝ) ^ 2 * (3 * b) ^ (2 * r + 3) * ∏ i ∈ Icc 1 k, |Y + 1 / 2 + u i|) *
        ((2 + c) ^ 2 * (k : ℝ) ^ 2 * (3 * b) ^ (2 * r + 3) * ∏ i ∈ Icc 1 k, |Y + 1 / 2 + v i|) :=
        mul_le_mul hP1 hP2 hQ (mul_nonneg hKc0 hPu)
    _ = ((2 + c) ^ 2 * (k : ℝ) ^ 2 * (3 * b) ^ (2 * r + 3)) *
          ((2 + c) ^ 2 * (k : ℝ) ^ 2 * (3 * b) ^ (2 * r + 3)) *
          ((∏ i ∈ Icc 1 k, |Y + 1 / 2 + u i|) * ∏ i ∈ Icc 1 k, |Y + 1 / 2 + v i|) := by ring
    _ ≤ (b ^ (4 * r + 10) * b ^ (4 * r + 10)) *
          ((∏ i ∈ Icc 1 k, |Y + 1 / 2 + u i|) * ∏ i ∈ Icc 1 k, |Y + 1 / 2 + v i|) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hKc hKc hKc0 (hKc0.trans hKc)) (mul_nonneg hPu hPv)
    _ = b ^ (8 * r + 20) *
          ((∏ i ∈ Icc 1 k, |Y + 1 / 2 + u i|) * ∏ i ∈ Icc 1 k, |Y + 1 / 2 + v i|) := by ring

end GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
