import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowTEqRowS
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MoorePowSubSelfEqProd

noncomputable section

namespace GlobalTheory.PMonE

open Finset

section Pw

variable {F : Type} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]

theorem coefDet_pw_natCast (n : ℕ) (x : F) : pw p (n : ℤ) x = x ^ p ^ n := by
  simp [pw]

theorem coefDet_pw_pow_p (k : ℤ) (x : F) : pw p k x ^ p = pw p (k + 1) x := by
  unfold pw
  by_cases hk : 0 ≤ k
  · rw [if_pos hk, if_pos (by omega), ← pow_mul, ← pow_succ]
    congr 2; omega
  · rw [if_neg hk]
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (-k).toNat = n + 1 := ⟨(-k).toNat - 1, by omega⟩
    rw [hn, Function.iterate_succ_apply']
    have e : ((frobeniusEquiv F p).symm (((frobeniusEquiv F p).symm)^[n] x)) ^ p =
        ((frobeniusEquiv F p).symm)^[n] x := by
      have := frobenius_apply_frobeniusEquiv_symm F p (((frobeniusEquiv F p).symm)^[n] x)
      rwa [frobenius_def] at this
    rw [e]
    by_cases hk1 : 0 ≤ k + 1
    · rw [if_pos hk1]
      have hn0 : n = 0 := by omega
      have h0 : (k + 1).toNat = 0 := by omega
      rw [hn0, h0]; simp
    · rw [if_neg hk1]; congr 1; omega

theorem coefDet_pw_pow (k : ℤ) (x : F) (a : ℕ) : pw p k x ^ p ^ a = pw p (k + a) x := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ, pow_mul, ih, coefDet_pw_pow_p]
    congr 1; push_cast; ring

end Pw

section Det

variable {F : Type} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]

theorem coefDet_det_scaled {h : ℕ} (a lam y : Fin h → F) :
    (Matrix.of fun r j : Fin h => (a r * (lam j * y j ^ p ^ (r : ℕ))) ^ p ^ (h - (r : ℕ))).det =
      (∏ r, a r ^ p ^ (h - (r : ℕ))) * ((∏ j, y j ^ p ^ h) *
        (Matrix.of fun r j : Fin h => lam j ^ p ^ (h - (r : ℕ))).det) := by
  rw [← Matrix.det_mul_row (fun j => y j ^ p ^ h), ← Matrix.det_mul_column (fun r => a r ^ p ^ (h - (r : ℕ)))]
  congr 1; ext r j
  simp only [Matrix.of_apply]
  have key : (y j ^ p ^ (r : ℕ)) ^ p ^ (h - (r : ℕ)) = y j ^ p ^ h := by
    rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' r.isLt.le]
  rw [mul_pow, mul_pow, key]
  ring

theorem coefDet_det_rev {h : ℕ} (lam : Fin h → F) :
    (Matrix.of fun r j : Fin h => lam j ^ p ^ (h - (r : ℕ))).det =
      ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin h)) : ℤ) : F) *
        (Matrix.of fun r j : Fin h => (lam j ^ p) ^ p ^ (r : ℕ)).det := by
  rw [← Matrix.det_permute]
  congr 1; ext r j
  simp only [Matrix.submatrix_apply, Matrix.of_apply, Fin.revPerm_apply, Fin.val_rev, id]
  rw [← pow_mul, ← pow_succ']
  congr 2; have := r.isLt; omega

theorem coefDet_orth_pow {h : ℕ} (lam : Fin h → F) (hO : Orth p lam) : Orth p (fun j => lam j ^ p) := by
  intro c j hc
  have h1 := hO c j hc
  have e : (∑ i, (c i : F) * lam i) ^ p = ∑ i, (c i : F) * lam i ^ p := by
    rw [← frobenius_def (R := F) p, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_intCast, frobenius_def]
  show ‖lam j ^ p‖ ≤ ‖∑ i, (c i : F) * lam i ^ p‖
  rw [← e, norm_pow, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h1 p

theorem coefDet_norm_sign_cast {n : Type} [Fintype n] [DecidableEq n] (σ : Equiv.Perm n) :
    ‖((Equiv.Perm.sign σ : ℤ) : F)‖ = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with e | e <;> simp [e]

end Det

end GlobalTheory.PMonE

end

namespace GlobalTheory.PMonE
open Finset

theorem coefB_det (F : Type) [NormedField F] [IsUltrametricDist F] (p : ℕ) [Fact p.Prime] [CharP F p]
    [PerfectRing F p] (h : ℕ) (ϖ : F) (hϖ : ϖ ≠ 0) (lam π : Fin h → F) (hl : ∀ j, lam j ≠ 0)
    (hπ : ∀ j, π j ≠ 0) (hA : Antitone (fun j => ‖lam j‖)) (hO : Orth p lam) (L U : ℕ) :
    ‖(coefB p ϖ lam π L U L).det‖ = 1 ∧ (coefB p ϖ lam π L U 0).det ≠ 0 := by
  set c : Fin h → F := fun r => lam r * π r ^ p ^ (r : ℕ) with hc
  have hc0 : ∀ r, c r ≠ 0 := fun r => mul_ne_zero (hl r) (pow_ne_zero _ (hπ r))
  have hA' : Antitone (fun j => ‖(fun j => lam j ^ p) j‖) := fun i j hij => by
    simp only [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hA hij) p
  have hDn : ‖(Matrix.of fun r j : Fin h => lam j ^ p ^ (h - (r : ℕ))).det‖ =
      ∏ j : Fin h, ‖lam j‖ ^ p ^ (h - (j : ℕ)) := by
    rw [coefDet_det_rev, norm_mul, coefDet_norm_sign_cast, one_mul]
    have hM := mooreNorm F p h (fun j => lam j ^ p) hA' (coefDet_orth_pow p lam hO)
    rw [hM]
    refine prod_congr rfl fun j _ => ?_
    rw [norm_pow, ← pow_mul, ← pow_succ']; congr 2; have := j.isLt; omega
  have hD0 : (Matrix.of fun r j : Fin h => lam j ^ p ^ (h - (r : ℕ))).det ≠ 0 := by
    rw [← norm_ne_zero_iff, hDn]
    exact (prod_pos fun j _ => pow_pos (norm_pos_iff.mpr (hl j)) _).ne'
  constructor
  · have e : coefB p ϖ lam π L U L = Matrix.of fun r j : Fin h =>
        ((c r)⁻¹ * (lam j * π j ^ p ^ (r : ℕ))) ^ p ^ (h - (r : ℕ)) := by
      ext r j
      simp only [coefB, Matrix.of_apply, term, le_add_iff_nonneg_right, zero_le, if_true, sub_self, neg_zero,
        zpow_zero, mul_one, zero_mul, add_zero, coefDet_pw_natCast, hc]
      rw [div_eq_inv_mul]
    rw [e, coefDet_det_scaled, norm_mul, norm_mul, norm_prod, norm_prod, hDn]
    have hX : ∏ r : Fin h, ‖c r‖ ^ p ^ (h - (r : ℕ)) =
        (∏ j : Fin h, ‖π j‖ ^ p ^ h) * ∏ j : Fin h, ‖lam j‖ ^ p ^ (h - (j : ℕ)) := by
      rw [← prod_mul_distrib]
      refine prod_congr rfl fun r _ => ?_
      rw [hc]
      simp only
      rw [norm_mul, norm_pow, mul_pow, ← pow_mul, ← pow_add, Nat.add_sub_cancel' r.isLt.le, mul_comm]
    have hX0 : ∏ r : Fin h, ‖c r‖ ^ p ^ (h - (r : ℕ)) ≠ 0 :=
      (prod_pos fun r _ => pow_pos (norm_pos_iff.mpr (hc0 r)) _).ne'
    simp only [norm_pow, norm_inv, inv_pow]
    rw [prod_inv_distrib, ← hX, inv_mul_cancel₀ hX0]
  · set y : Fin h → F := fun j => pw p (-((L : ℤ) * h)) (π j) with hy
    have hy0 : ∀ j, y j ≠ 0 := by
      intro j hyj
      have h1 := coefDet_pw_pow p (-((L : ℤ) * h)) (π j) (L * h)
      have h0 : pw p (0 : ℤ) (π j) = π j := by simp [pw]
      rw [show pw p (-((L : ℤ) * h)) (π j) = y j from rfl, hyj,
        zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)] at h1
      push_cast at h1
      rw [neg_add_cancel, h0] at h1
      exact hπ j h1.symm
    have e : coefB p ϖ lam π L U 0 = Matrix.of fun r j : Fin h =>
        ((ϖ ^ L / c r) * (lam j * y j ^ p ^ (r : ℕ))) ^ p ^ (h - (r : ℕ)) := by
      ext r j
      simp only [coefB, Matrix.of_apply, term, zero_le, if_true, hc, hy, coefDet_pw_pow]
      have e1 : ((r : ℕ) : ℤ) + (((0 : ℕ) : ℤ) - L) * h = -((L : ℤ) * h) + ((r : ℕ) : ℤ) := by
        push_cast; ring
      have e2 : ϖ ^ (-(((0 : ℕ) : ℤ) - L)) = ϖ ^ L := by
        rw [show -(((0 : ℕ) : ℤ) - L) = (L : ℤ) by push_cast; ring, zpow_natCast]
      rw [e1, e2]
      congr 1
      ring
    rw [e, coefDet_det_scaled]
    exact mul_ne_zero (prod_ne_zero_iff.mpr fun r _ => pow_ne_zero _ (div_ne_zero (pow_ne_zero _ hϖ) (hc0 r)))
      (mul_ne_zero (prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ (hy0 j)) hD0)

end GlobalTheory.PMonE
