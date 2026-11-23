import Mathlib

namespace GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid

open Finset

def Pst (k r : ℕ) (lam : ℕ → ℝ) (c Y : ℝ) : ℝ := ∏ s ∈ Icc 1 (k + 2 * r + 1), (|Y + lam s| + c)

theorem Pst_pos (k r : ℕ) (lam : ℕ → ℝ) {c : ℝ} (hc : 0 < c) (Y : ℝ) : 0 < Pst k r lam c Y := by
  unfold Pst
  exact Finset.prod_pos fun s _ => add_pos_of_nonneg_of_pos (abs_nonneg _) hc

def PairOK (k : ℕ) (lam v : ℕ → ℝ) (e : ℕ) (x : ℝ) : Prop :=
  ∀ s, 1 ≤ s → s ≤ k - 1 → s ≠ e →
    (x < lam s → lam s + 1 / 2 ≤ v s) ∧ (lam s ≤ x → v (s + 1) ≤ lam s - 1 / 2)

theorem pairOK_of_interlace (k : ℕ) (lam v : ℕ → ℝ) (e : ℕ) (x : ℝ)
    (h : ∀ s, 1 ≤ s → s ≤ k - 1 → lam s + 1 / 2 ≤ v s ∧ v (s + 1) ≤ lam s - 1 / 2) :
    PairOK k lam v e x := by
  intro s hs1 hsk _
  exact ⟨fun _ => (h s hs1 hsk).1, fun _ => (h s hs1 hsk).2⟩

theorem pairOK_moved (k l : ℕ) (lam u v : ℕ → ℝ) (x : ℝ)
    (h : ∀ s, 1 ≤ s → s ≤ k - 1 → lam s + 1 / 2 ≤ u s ∧ u (s + 1) ≤ lam s - 1 / 2)
    (hv : ∀ i, i ≠ l → i ≠ l + 1 → v i = u i)
    (hlow : ∀ s, 1 ≤ s → s < l → x < lam s) (hhigh : ∀ s, l < s → s ≤ k - 1 → lam s ≤ x) :
    PairOK k lam v l x := by
  intro s hs1 hsk hsl
  rcases lt_or_gt_of_ne hsl with hlt | hgt
  · have hx := hlow s hs1 hlt
    refine ⟨fun _ => ?_, fun hle => absurd hx (not_lt.mpr hle)⟩
    rw [hv s (by omega) (by omega)]
    exact (h s hs1 hsk).1
  · have hx := hhigh s hgt hsk
    refine ⟨fun hlt => absurd hx (not_le.mpr hlt), fun _ => ?_⟩
    rw [hv (s + 1) (by omega) (by omega)]
    exact (h s hs1 hsk).2

end GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
