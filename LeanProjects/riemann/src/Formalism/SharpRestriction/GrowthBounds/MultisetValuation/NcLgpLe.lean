import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NumericalClosedOfNeed

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Finset

theorem nc_lgp_le (p : ℕ) (hp : 2 ≤ p) (x : ℤ) (A : ℝ) (c : ℕ) (_hA : 1 ≤ A) (hx : (x : ℝ) ≤ A ^ c)
    (hl : 1 ≤ Real.logb p A) : (lgp p x : ℝ) ≤ (c + 1) * Real.logb p A := by
  unfold lgp
  split_ifs with h
  · push_cast
    have : 0 ≤ Real.logb p A := by linarith
    nlinarith
  · push_cast
    have hx0 : 0 < x := by omega
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
    have h1 : (Nat.log p x.toNat : ℝ) ≤ Real.logb p (x.toNat : ℝ) := Real.natLog_le_logb _ _
    have h2 : ((x.toNat : ℕ) : ℝ) = (x : ℝ) := by
      have : ((x.toNat : ℕ) : ℤ) = x := Int.toNat_of_nonneg hx0.le
      exact_mod_cast this
    rw [h2] at h1
    have h3 : Real.logb p (x : ℝ) ≤ Real.logb p (A ^ c) :=
      Real.logb_le_logb_of_le hp1 (by exact_mod_cast hx0) hx
    rw [Real.logb_pow] at h3
    nlinarith

variable {n' k1 : ℕ}

theorem nc_de_le (p t : ℕ) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ) (j : ℕ)
    (hp : 2 ≤ p) (A : ℝ) (NM : ℝ) (hA : 1 ≤ A) (hl : 1 ≤ Real.logb p A) (hN1 : (NN k1 t j : ℝ) ≤ NM)
    (hN0 : (NN k1 t (j - 1) : ℝ) ≤ NM) (hal : ∀ s, (al TT lam0 s : ℝ) ≤ A ^ 2)
    (hls : ∀ s, (lsz t TT lam0 w j s : ℝ) ≤ A ^ 4) :
    de p t TT lam0 w j ≤ 8 * (n' : ℝ) * NM ^ 2 * Real.logb p A + 9 * (TT.card : ℝ) * Real.logb p A ^ 2 := by
  unfold de
  set ℓ := Real.logb p A with hℓ
  have hN1' : (1 : ℝ) ≤ NN k1 t j := by unfold NN; push_cast; nlinarith
  have hNM : 1 ≤ NM := le_trans hN1' hN1
  have hN0' : (0 : ℝ) ≤ NN k1 t (j - 1) := by positivity
  have hα : ∀ s, (lgp p (al TT lam0 s) : ℝ) ≤ 3 * ℓ := fun s => by
    have := nc_lgp_le p hp _ A 2 hA (hal s) hl; push_cast at this; linarith
  have hlz : ∀ s, (lgp p (lsz t TT lam0 w j s) : ℝ) ≤ 5 * ℓ := fun s => by
    have := nc_lgp_le p hp _ A 4 hA (hls s) hl; push_cast at this; linarith
  have hα0 : ∀ s, (0 : ℝ) ≤ lgp p (al TT lam0 s) := fun s => by positivity
  have hlz0 : ∀ s, (0 : ℝ) ≤ lgp p (lsz t TT lam0 w j s) := fun s => by positivity
  have h1 : ∑ s : Fin n', ((NN k1 t j : ℝ) * lgp p (al TT lam0 s) +
      (NN k1 t (j - 1) : ℝ) * (NN k1 t j : ℝ) * lgp p (lsz t TT lam0 w j s)) ≤
      ∑ _s : Fin n', (8 * NM ^ 2 * ℓ) := by
    apply Finset.sum_le_sum
    intro s _
    have e1 : (NN k1 t j : ℝ) * lgp p (al TT lam0 s) ≤ NM * (3 * ℓ) :=
      mul_le_mul hN1 (hα s) (hα0 s) (by linarith)
    have e2 : (NN k1 t (j - 1) : ℝ) * (NN k1 t j : ℝ) * lgp p (lsz t TT lam0 w j s) ≤ NM * NM * (5 * ℓ) :=
      mul_le_mul (mul_le_mul hN0 hN1 (by positivity) (by linarith)) (hlz s) (hlz0 s) (by nlinarith)
    have e3 : NM * (3 * ℓ) ≤ NM * NM * (3 * ℓ) := by
      have : 0 ≤ NM * (3 * ℓ) := by positivity
      nlinarith
    nlinarith
  have h2 : ∑ s ∈ TT, ((lgp p (al TT lam0 s) : ℝ)) ^ 2 ≤ ∑ _s ∈ TT, (9 * ℓ ^ 2) := by
    apply Finset.sum_le_sum
    intro s _
    have := hα s
    have := hα0 s
    nlinarith
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
  rw [Finset.sum_const, nsmul_eq_mul] at h2
  nlinarith

end Formalism.MainNotions.FormalGroupSystem.Pf
