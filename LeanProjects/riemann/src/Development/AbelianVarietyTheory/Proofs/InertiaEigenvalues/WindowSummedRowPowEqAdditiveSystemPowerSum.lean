import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowTEqRowS
open GlobalTheory.PMonE

open Finset
namespace GlobalTheory.PMonE.WinCoef
variable {F : Type} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]

noncomputable abbrev frobAut : RingAut F := frobeniusEquiv F p

theorem frob_pow_apply (n : ℕ) (x : F) : ((frobAut (F := F) p) ^ n) x = x ^ p ^ n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, RingAut.mul_apply, ih]
    simp only [frobAut, frobeniusEquiv_apply, frobenius_def, ← pow_mul, pow_succ]
    rw [mul_comm]

theorem frob_inv_pow_apply (n : ℕ) (x : F) :
    (((frobAut (F := F) p)⁻¹) ^ n) x = ((frobeniusEquiv F p).symm)^[n] x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Function.iterate_succ_apply, RingAut.mul_apply, ih, RingAut.inv_apply]

theorem pw_eq (k : ℤ) (x : F) : pw p k x = ((frobAut (F := F) p) ^ k) x := by
  unfold pw
  split_ifs with hk
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [zpow_natCast, frob_pow_apply]
    simp
  · obtain ⟨n, hn⟩ := Int.exists_eq_neg_ofNat (le_of_lt (not_le.mp hk))
    subst hn
    rw [zpow_neg, zpow_natCast, ← inv_pow, frob_inv_pow_apply]
    simp

theorem pw_mul (k : ℤ) (a b : F) : pw p k (a * b) = pw p k a * pw p k b := by
  rw [pw_eq, pw_eq, pw_eq, map_mul]

theorem pw_win (h r L : ℕ) (hr : r ≤ h) (hL : 1 ≤ L) (n : ℤ) (hn : -(L : ℤ) ≤ n) (z : F) :
    pw p ((r : ℤ) + n * h) (z ^ (p ^ h) ^ (L - 1)) ^ p ^ (h - r) = z ^ (p ^ h) ^ ((n + L).toNat) := by
  have e1 : z ^ (p ^ h) ^ (L - 1) = ((frobAut (F := F) p) ^ (((h * (L - 1) : ℕ)) : ℤ)) z := by
    rw [zpow_natCast, frob_pow_apply, pow_mul]
  have e2 : z ^ (p ^ h) ^ ((n + L).toNat) =
      ((frobAut (F := F) p) ^ (((h * (n + L).toNat : ℕ)) : ℤ)) z := by
    rw [zpow_natCast, frob_pow_apply, pow_mul]
  have e3 : ∀ y : F, y ^ p ^ (h - r) = ((frobAut (F := F) p) ^ (((h - r : ℕ)) : ℤ)) y := fun y => by
    rw [zpow_natCast, frob_pow_apply]
  rw [e3, pw_eq, e1, e2, ← RingAut.mul_apply, ← RingAut.mul_apply, ← zpow_add, ← zpow_add]
  congr 2
  have ht : ((n + L).toNat : ℤ) = n + L := Int.toNat_of_nonneg (by omega)
  push_cast [Nat.cast_sub hr, Nat.cast_sub hL, ht]
  ring

end GlobalTheory.PMonE.WinCoef

open GlobalTheory.PMonE.WinCoef in

theorem GlobalTheory.PMonE.rowS_winPt_pow_eq_gsum_coefB (F : Type) [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (h : ℕ)
    (ϖ : F) (lam π : Fin h → F) (L U : ℕ) : 1 ≤ L → ∀ (z : Fin h → F) (r : Fin h),
    (rowS p ϖ lam L U (winPt p π L z) r / (lam r * π r ^ p ^ (r : ℕ))) ^ p ^ (h - (r : ℕ)) =
      gsum (p ^ h) (L + U) (coefB p ϖ lam π L U) z r := by
  intro hL z r
  have hr : (r : ℕ) ≤ h := r.isLt.le
  simp only [rowS, winPt, gsum, Finset.sum_apply, Matrix.mulVec, dotProduct, coefB, Matrix.of_apply]
  rw [Finset.sum_comm (s := Finset.range (L + U + 1)), Finset.sum_div, sum_pow_char_pow]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_div, sum_pow_char_pow]
  refine Finset.sum_nbij' (fun n => (n + L).toNat) (fun m => (m : ℤ) - L) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_Icc, Finset.mem_range] at hn ⊢
    omega
  · intro m hm
    simp only [Finset.mem_Icc, Finset.mem_range] at hm ⊢
    omega
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    omega
  · intro m hm
    simp
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    have ht : ((n + L).toNat : ℤ) = n + L := Int.toNat_of_nonneg (by omega)
    have hle : (n + L).toNat ≤ L + U := by omega
    have hsub : (((n + L).toNat : ℕ) : ℤ) - L = n := by omega
    rw [if_pos hle, hsub, term, term, winPt, pw_mul, ← pw_win p h r L hr hL n hn.1 (z j)]
    rw [show lam j * ϖ ^ (-n) * (pw p (↑↑r + n * ↑h) (π j) * pw p (↑↑r + n * ↑h) (z j ^ (p ^ h) ^ (L - 1))) /
        (lam r * π r ^ p ^ (r : ℕ)) = (lam j * ϖ ^ (-n) * pw p (↑↑r + n * ↑h) (π j) / (lam r * π r ^ p ^ (r : ℕ))) *
        pw p (↑↑r + n * ↑h) (z j ^ (p ^ h) ^ (L - 1)) by ring, mul_pow]
