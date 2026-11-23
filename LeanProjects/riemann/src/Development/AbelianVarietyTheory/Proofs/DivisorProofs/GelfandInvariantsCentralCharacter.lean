import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Tpr
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CapelliOfGelfand
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QminorPolyMap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QdetAddOneSubEqSumQminorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TracedQminorComatrixTruncatedInverseStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarCapelliTruncatedPerelomovPopovStatement

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WignerGL GlobalTheory.WigAlg Formalism.REAL
open scoped TensorProduct

namespace GlobalTheory.GelfandOfCapelli

open Finset Polynomial
open GlobalTheory.Dec (gelfVal)

theorem main_succ (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (F : Fin (m+1) → Fin (m+1) → A)
    (χ : Fin (m+1) → ℂ) (hF : GlRel F)
    (hq : ∀ w : ℂ, qdet F w = algebraMap ℂ A ((GlobalTheory.CapelliNewton.capQ m χ).eval w)) (N : ℕ) :
    etr F N = algebraMap ℂ A (gelfVal χ N) := by
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).mp fun φ => ?_
  set Q := GlobalTheory.CapelliNewton.capQ m χ with hQ
  have hmin : ∀ i j : Fin (m + 1), ∃ c' : ℕ → A, ∀ w : ℂ,
      qminor F (Fin.succAbove j) (Fin.succAbove i) w = ∑ d ∈ range (m + 1), w ^ d • c' d := by
    intro i j
    obtain ⟨c', hc'⟩ := GlobalTheory.qminor_polyMap A (m + 1) m F (Fin.succAbove j) (Fin.succAbove i) 0
    exact ⟨c', fun w => by simpa using hc' w⟩
  choose cm hcm using hmin
  let Rc : ℕ → A := fun d => ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
    (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) * cm i j d * epow F (N + 1) j i
  have hR : ∀ w : ℂ, ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) *
      qminor F (Fin.succAbove j) (Fin.succAbove i) w * epow F (N + 1) j i
      = ∑ d ∈ range (m + 1), w ^ d • Rc d := by
    intro w
    simp only [Rc, hcm, mul_sum, sum_mul, smul_sum, mul_smul_comm, smul_mul_assoc]
    conv_lhs => enter [2, x]; rw [sum_comm]
    rw [sum_comm]
  let Rp : ℂ[X] := ∑ d ∈ range (m + 1), C (φ (Rc d)) * X ^ d
  have hRp : ∀ w : ℂ, φ (∑ d ∈ range (m + 1), w ^ d • Rc d) = Rp.eval w := by
    intro w
    simp only [Rp, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X, map_sum, map_smul, smul_eq_mul]
    exact sum_congr rfl fun d _ => mul_comm _ _
  have hRpdeg : Rp.natDegree ≤ m := natDegree_sum_le_of_forall_le _ _ fun i hi =>
    (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp (mem_range.mp hi))
  have hφa : ∀ c : ℂ, φ (algebraMap ℂ A c) = c * φ 1 := fun c => by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul]
  have hrec : ∀ w : ℂ, (w - m) ^ (N + 1) * (Q.eval (w + 1) - Q.eval w) * φ 1 + (-1) ^ N * Rp.eval w
      = Q.eval w * ∑ k ∈ range (N + 1), (-1) ^ k * (w - m) ^ (N - k) * φ (etr F k) := by
    intro w
    have h1 := congrArg φ (GlobalTheory.T.traced_qminor_comatrix_truncated_inverse A m F hF w N)
    rw [← GlobalTheory.T.qdet_add_one_sub_eq_sum_qminor', hR] at h1
    simp only [hq, ← Algebra.smul_def, map_add, map_smul, smul_eq_mul, hRp] at h1
    simp only [mul_sum, map_sum, map_smul, map_sub, smul_eq_mul, hφa] at h1
    rw [mul_sum]
    linear_combination h1
  obtain ⟨rs, hrs, hrsE⟩ := GlobalTheory.T.scalar_capelli_truncated_perelomov_popov m N χ
  let S : ℂ[X] := ∑ k ∈ range (N + 1),
    C ((-1) ^ k * (φ (etr F k) - gelfVal χ k * φ 1)) * (X - C (m : ℂ)) ^ (N - k)
  have hSe : ∀ w : ℂ, S.eval w = (∑ k ∈ range (N + 1), (-1) ^ k * (w - m) ^ (N - k) * φ (etr F k))
      - φ 1 * ∑ k ∈ range (N + 1), (-1) ^ k * (w - m) ^ (N - k) * gelfVal χ k := by
    intro w
    simp only [S, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_sub, eval_X, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun k _ => by ring
  have hQS : Q * S = C ((-1) ^ N) * Rp + C (φ 1) * rs := by
    refine Polynomial.funext fun w => ?_
    have h2 := hrsE w
    rw [← GlobalTheory.CapelliNewton.capQ_eval m χ (w + 1), ← GlobalTheory.CapelliNewton.capQ_eval m χ w, ← hQ] at h2
    simp only [eval_mul, eval_add, eval_C, hSe]
    linear_combination -hrec w + φ 1 * h2
  have hS0 : S = 0 := by
    by_contra hne
    have hd := (GlobalTheory.CapelliNewton.capQ_monic m χ).natDegree_mul' hne
    rw [← hQ, hQS, GlobalTheory.CapelliNewton.capQ_natDegree] at hd
    have hle : (C ((-1 : ℂ) ^ N) * Rp + C (φ 1) * rs).natDegree ≤ m :=
      (natDegree_add_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans hRpdeg)
        ((natDegree_C_mul_le _ _).trans hrs))
    omega
  have h0 := congrArg (eval (m : ℂ)) hS0
  simp only [S, eval_zero, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_sub, eval_X, sub_self] at h0
  rw [sum_eq_single N (fun b hb hbN => by
      rw [zero_pow (Nat.sub_ne_zero_of_lt (lt_of_le_of_ne (Nat.lt_succ_iff.mp (mem_range.mp hb)) hbN)), mul_zero])
    (fun h => absurd (self_mem_range_succ N) h)] at h0
  rw [Nat.sub_self, pow_zero, mul_one] at h0
  have hne : ((-1 : ℂ)) ^ N ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [map_sub, hφa]
  exact mul_left_cancel₀ hne (by linear_combination h0)

theorem gelfand_of_capelli : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (F : Fin n → Fin n → A) (χ : Fin n → ℂ),
    GlRel F → (∀ u : ℂ, qdet F (u + ((n : ℂ) - 1) / 2) = algebraMap ℂ A (∏ s, (u + χ s))) →
    ∀ k : ℕ, etr F (k + 1) = algebraMap ℂ A (GlobalTheory.Dec.gelfVal χ (k + 1)) := by
  intro A _ _ n F χ hF hq k
  cases n with
  | zero => simp [etr, gelfVal]
  | succ m =>
    refine main_succ A m F χ hF (fun w => ?_) (k + 1)
    calc qdet F w = qdet F ((w - (m : ℂ) / 2) + (((m + 1 : ℕ) : ℂ) - 1) / 2) := by congr 1; push_cast; ring
      _ = algebraMap ℂ A (∏ s, ((w - (m : ℂ) / 2) + χ s)) := hq _
      _ = _ := by rw [GlobalTheory.CapelliNewton.capQ_eval]

end GlobalTheory.GelfandOfCapelli
