import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm

noncomputable section

namespace GlobalTheory.PMonE

open Finset Polynomial

theorem moore_pow_sub_self_eq_prod {F : Type*} [Field F] (p : ℕ) [Fact p.Prime] [CharP F p] (x : F) :
    x ^ p - x = ∏ c : ZMod p, (x - ((c.val : ℕ) : F)) := by
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hroots := FiniteField.roots_X_pow_card_sub_X (ZMod p)
  rw [ZMod.card] at hroots
  have hdeg : (X ^ p - X : (ZMod p)[X]).natDegree = p := FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod p) hp
  have hmon : (X ^ p - X : (ZMod p)[X]).Monic := by
    apply Polynomial.monic_X_pow_sub
    rw [Polynomial.degree_X]
    exact_mod_cast hp
  have h := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon (by
    rw [hroots, hdeg]; simp)
  rw [hroots] at h
  have h2 : (X ^ p - X : (ZMod p)[X]) = ∏ c : ZMod p, (X - C c) := by
    rw [← h]; rfl
  have h3 := congrArg (Polynomial.aeval x) h2
  simp only [map_sub, map_pow, aeval_X, map_prod, aeval_C] at h3
  rw [h3]
  refine Finset.prod_congr rfl fun c _ => ?_
  congr 1
  conv_lhs => rw [← ZMod.natCast_zmod_val c]
  rw [map_natCast]

theorem moore_step_eq_prod {F : Type*} [Field F] (p : ℕ) [Fact p.Prime] [CharP F p] (x t : F) :
    x ^ p - t ^ (p - 1) * x = ∏ c : ZMod p, (x - ((c.val : ℕ) : F) * t) := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  by_cases ht : t = 0
  · subst ht
    rw [zero_pow (by omega)]
    simp
  · have h := moore_pow_sub_self_eq_prod p (x / t)
    have h1 : ∏ c : ZMod p, (x - ((c.val : ℕ) : F) * t) = ∏ c : ZMod p, (t * (x / t - ((c.val : ℕ) : F))) := by
      refine Finset.prod_congr rfl fun c _ => ?_
      field_simp
    rw [h1, Finset.prod_mul_distrib, ← h, Finset.prod_const, Finset.card_univ, ZMod.card]
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    simp only [Nat.add_sub_cancel, div_pow]
    field_simp
    ring

theorem moore_step_norm_ge {F : Type*} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] (x t : F) (r : ℝ)
    (hr : 0 ≤ r) (h : ∀ c : ℤ, r ≤ ‖x + (c : F) * t‖) : r ^ p ≤ ‖x ^ p - t ^ (p - 1) * x‖ := by
  rw [moore_step_eq_prod, norm_prod]
  have : r ^ p = ∏ _c : ZMod p, r := by simp
  rw [this]
  refine Finset.prod_le_prod (fun _ _ => hr) fun c _ => ?_
  have := h (-(c.val : ℤ))
  simpa only [Int.cast_neg, Int.cast_natCast, neg_mul, ← sub_eq_add_neg] using this

theorem moore_step_norm_le {F : Type*} [NormedField F] [IsUltrametricDist F] (p : ℕ) [Fact p.Prime] (x t : F)
    (h : ‖t‖ ≤ ‖x‖) : ‖x ^ p - t ^ (p - 1) * x‖ ≤ ‖x‖ ^ p := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  rw [sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_pow]
  · rw [norm_neg, norm_mul, norm_pow]
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    simp only [Nat.add_sub_cancel, pow_succ]
    gcongr

theorem moore_step_sum {F : Type*} [Field F] (p : ℕ) [Fact p.Prime] [CharP F p] {h : ℕ} (c : Fin h → ℤ)
    (x : Fin h → F) (t : F) :
    ∑ i, (c i : F) * (x i ^ p - t ^ (p - 1) * x i) =
      (∑ i, (c i : F) * x i) ^ p - t ^ (p - 1) * ∑ i, (c i : F) * x i := by
  rw [sum_pow_char, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (c i : F) ^ p = c i := by
    have := map_intCast (frobenius F p) (c i)
    rwa [frobenius_def] at this
  rw [mul_pow, this]
  ring

theorem moore_det_succ {F : Type*} [Field F] (p : ℕ) [Fact p.Prime] [CharP F p] {k : ℕ} (lam : Fin (k + 1) → F) :
    (Matrix.of fun r j : Fin (k + 1) => lam j ^ p ^ (r : ℕ)).det =
      (-1) ^ k * lam (Fin.last k) * (Matrix.of fun r j : Fin k =>
        (lam j.castSucc ^ p - lam (Fin.last k) ^ (p - 1) * lam j.castSucc) ^ p ^ (r : ℕ)).det := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  set t := lam (Fin.last k) with ht
  let B : Matrix (Fin (k + 1)) (Fin (k + 1)) F :=
    Matrix.of fun r j => Fin.cases (motive := fun _ => F) (lam j)
      (fun s => (lam j ^ p - t ^ (p - 1) * lam j) ^ p ^ (s : ℕ)) r
  have hB : (Matrix.of fun r j : Fin (k + 1) => lam j ^ p ^ (r : ℕ)).det = B.det := by
    refine Matrix.det_eq_of_forall_row_eq_smul_add_pred (fun s => (t ^ (p - 1)) ^ p ^ (s : ℕ)) ?_ ?_
    · intro j; simp [B]
    · intro i j
      simp only [B, Matrix.of_apply, Fin.cases_succ, Fin.val_succ, Fin.val_castSucc]
      rw [sub_pow_char_pow, mul_pow, ← pow_mul (lam j) p, pow_succ' p]
      ring
  have h0 : t ^ p - t ^ (p - 1) * t = 0 := by
    rw [← pow_succ, Nat.sub_add_cancel hp.le, sub_self]
  rw [hB, Matrix.det_succ_column B (Fin.last k), Fin.sum_univ_succ, Finset.sum_eq_zero, add_zero]
  · congr 1
    · simp [B, ht]
    · congr 1
      ext r j
      simp [B]
  · intro i _
    have : B i.succ (Fin.last k) = 0 := by
      simp only [B, Matrix.of_apply, Fin.cases_succ, ← ht, h0]
      exact zero_pow (pow_ne_zero _ (by omega))
    rw [this]; simp

theorem mooreNorm : MooreNorm := by
  intro F _ _ p _ _ _ h
  induction h with
  | zero => intro lam _ _; simp
  | succ k ih =>
    intro lam hanti horth
    set t := lam (Fin.last k) with ht
    have hlow : ∀ (c : Fin k → ℤ) (j : Fin k), ¬ (p : ℤ) ∣ c j →
        ‖lam j.castSucc‖ ^ p ≤ ‖∑ i, (c i : F) * (lam i.castSucc ^ p - t ^ (p - 1) * lam i.castSucc)‖ := by
      intro c j hc
      rw [moore_step_sum p c (fun i => lam i.castSucc) t]
      refine moore_step_norm_ge p _ _ _ (norm_nonneg _) fun d => ?_
      have := horth (Fin.snoc (α := fun _ => ℤ) c d) j.castSucc (by simpa using hc)
      rw [Fin.sum_univ_castSucc] at this
      simpa using this
    have hnorm : ∀ j : Fin k, ‖lam j.castSucc ^ p - t ^ (p - 1) * lam j.castSucc‖ = ‖lam j.castSucc‖ ^ p := by
      intro j
      refine le_antisymm (moore_step_norm_le p _ _ (hanti (Fin.le_last _))) ?_
      have := hlow (Pi.single j 1) j (by
        simp only [Pi.single_eq_same]
        exact (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)).not_dvd_one)
      rw [Finset.sum_eq_single j] at this
      · simpa using this
      · intro b _ hb; simp [hb]
      · simp
    have hih := ih (fun j => lam j.castSucc ^ p - t ^ (p - 1) * lam j.castSucc) (by
      intro a b hab
      simp only [hnorm]
      exact pow_le_pow_left₀ (norm_nonneg _) (hanti (Fin.castSucc_le_castSucc_iff.mpr hab)) _) (by
      intro c j hc
      simp only [hnorm]
      exact hlow c j hc)
    rw [moore_det_succ, norm_mul, norm_mul, ← ht, hih, Fin.prod_univ_castSucc]
    simp only [hnorm, norm_pow, norm_neg, norm_one, one_pow, one_mul, Fin.val_last, Nat.add_sub_cancel,
      Nat.sub_self, pow_zero, pow_one, Fin.val_castSucc, ← ht]
    rw [mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← pow_mul, ← pow_succ']
    congr 2
    have := j.isLt
    omega

end GlobalTheory.PMonE

end
