import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.AltCoeffRho

noncomputable section
open MvPolynomial Finset GlobalTheory.FlagHook Formalism.DegreeFormula

namespace GlobalTheory.FlagHookShift

def shiftE {N : ℕ} (n : Fin N → ℕ) : Polynomial (MvPolynomial (Fin N) ℝ) :=
  Matrix.det (Matrix.of fun i c : Fin N =>
    Polynomial.C (C (((n c).factorial : ℝ)⁻¹)) * (Polynomial.X + Polynomial.C (X i)) ^ n c)

theorem shiftE_eq_zero {N : ℕ} (n : Fin N → ℕ) {c d : Fin N} (h : c ≠ d) (hn : n c = n d) :
    shiftE n = 0 := by
  unfold shiftE
  apply Matrix.det_zero_of_column_eq h
  intro k
  simp [hn]

theorem eval_shiftE {N : ℕ} (n : Fin N → ℕ) (a : ℝ) :
    (shiftE n).eval (C a) =
      aeval (fun i : Fin N => (X i + C a : MvPolynomial (Fin N) ℝ)) (detE n) := by
  unfold shiftE detE
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det, AlgHom.map_det]
  congr 1
  ext1 i c
  simp [add_comm]

theorem eval_zero_shiftE {N : ℕ} (n : Fin N → ℕ) : (shiftE n).eval 0 = detE n := by
  have := eval_shiftE n 0
  simpa using this

theorem derivative_entry {N : ℕ} (m : ℕ) (i : Fin N) :
    Polynomial.derivative (Polynomial.C (C (((m + 1).factorial : ℝ)⁻¹)) *
      (Polynomial.X + Polynomial.C (X i : MvPolynomial (Fin N) ℝ)) ^ (m + 1)) =
    Polynomial.C (C ((m.factorial : ℝ)⁻¹)) * (Polynomial.X + Polynomial.C (X i)) ^ m := by
  rw [Polynomial.derivative_C_mul, Polynomial.derivative_X_add_C_pow, ← mul_assoc, ← map_mul]
  congr 2
  rw [← map_natCast (C : ℝ →+* MvPolynomial (Fin N) ℝ), ← map_mul]
  congr 1
  rw [Nat.factorial_succ]
  have : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have h2 : ((m : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp

theorem derivative_shiftE {N : ℕ} (n : Fin N → ℕ) :
    Polynomial.derivative (shiftE n) =
      ∑ c, if n c = 0 then 0 else shiftE (Function.update n c (n c - 1)) := by
  unfold shiftE
  simp only [Matrix.det_apply', Matrix.of_apply]
  rw [Polynomial.derivative_sum]
  simp only [Polynomial.derivative_intCast_mul, Polynomial.derivative_prod_finset, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs with h
  · simp [h]
  · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero h
    refine Finset.sum_congr rfl fun σ _ => ?_
    congr 1
    rw [← Finset.prod_erase_mul univ _ (mem_univ c)]
    congr 1
    · refine Finset.prod_congr rfl fun b hb => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hb)]
    · rw [Function.update_self, hm, derivative_entry]
      simp

theorem derivative_shiftE_rho (N : ℕ) : Polynomial.derivative (shiftE (rho N)) = 0 := by
  rw [derivative_shiftE]
  refine Finset.sum_eq_zero fun c _ => ?_
  split_ifs with h
  · rfl
  · simp only [rho] at h
    have hc : (c : ℕ) + 1 < N := by omega
    have hne : (⟨c + 1, hc⟩ : Fin N) ≠ c := by
      intro e; have := congrArg Fin.val e; simp at this
    apply shiftE_eq_zero _ hne
    rw [Function.update_self, Function.update_of_ne hne]
    simp only [rho]
    omega

theorem lower_hook_zero {N k r : ℕ} (c : Fin N) (h0 : (c : ℕ) ≠ 0) (hr : (c : ℕ) ≠ r) :
    (if hookRho N k r c = 0 then 0
      else shiftE (Function.update (hookRho N k r) c (hookRho N k r c - 1))) = 0 ∨
    ((c : ℕ) + 1 = N ∧ (c : ℕ) < r) := by
  by_cases hc : (c : ℕ) + 1 < N
  · left
    split_ifs with h
    · rfl
    · have hne : (⟨c + 1, hc⟩ : Fin N) ≠ c := by
        intro e; have := congrArg Fin.val e; simp at this
      apply shiftE_eq_zero _ hne
      rw [Function.update_self, Function.update_of_ne hne]
      simp only [hookRho]
      split_ifs <;> first | contradiction | omega
  · have := c.2
    by_cases h2 : (c : ℕ) < r
    · right; omega
    · left
      rw [if_pos]
      simp only [hookRho]
      split_ifs <;> first | contradiction | omega

theorem derivative_shiftE_hook {N k r : ℕ} (hr : r < k) (hk : k ≤ N) :
    Polynomial.derivative (shiftE (hookRho N k r)) =
      shiftE (hookRho N (k - 1) r) + if r = 0 then 0 else shiftE (hookRho N (k - 1) (r - 1)) := by
  rw [derivative_shiftE]
  have hN : 0 < N := by omega
  have hrN : r < N := by omega
  have e0 : (if hookRho N k r ⟨0, hN⟩ = 0 then 0
      else shiftE (Function.update (hookRho N k r) ⟨0, hN⟩ (hookRho N k r ⟨0, hN⟩ - 1))) =
      shiftE (hookRho N (k - 1) r) := by
    rw [if_neg (by simp only [hookRho]; simp; omega)]
    congr 1
    funext c
    by_cases hc : c = ⟨0, hN⟩
    · subst hc
      rw [Function.update_self]
      simp only [hookRho, if_true]
      omega
    · rw [Function.update_of_ne hc]
      have : (c : ℕ) ≠ 0 := fun e => hc (Fin.ext e)
      simp [hookRho, this]
  have hz : ∀ c : Fin N, c ≠ ⟨0, hN⟩ → c ≠ ⟨r, hrN⟩ → (if hookRho N k r c = 0 then 0
      else shiftE (Function.update (hookRho N k r) c (hookRho N k r c - 1))) = 0 := by
    intro c h0 h1
    have := c.2
    rcases lower_hook_zero (k := k) (r := r) c (fun e => h0 (Fin.ext e))
      (fun e => h1 (Fin.ext e)) with h | h
    · exact h
    · omega
  by_cases h : r = 0
  · rw [if_pos h, add_zero, Finset.sum_eq_single ⟨0, hN⟩, e0]
    · intro c _ hc
      exact hz c hc (by subst h; exact hc)
    · simp
  · rw [if_neg h, Finset.sum_eq_add (⟨0, hN⟩ : Fin N) ⟨r, hrN⟩, e0]
    · congr 1
      rw [if_neg (by simp [hookRho, h])]
      congr 1
      funext c
      by_cases hc : c = ⟨r, hrN⟩
      · subst hc
        rw [Function.update_self]
        simp only [hookRho]
        split_ifs <;> first | contradiction | omega
      · rw [Function.update_of_ne hc]
        have : (c : ℕ) ≠ r := fun e => hc (Fin.ext e)
        simp only [hookRho]
        split_ifs <;> first | contradiction | omega
    · intro e; exact h (congrArg Fin.val e).symm
    · intro c _ hc
      exact hz c hc.1 hc.2
    · simp
    · simp

theorem telescope {R : Type} [CommRing R] (T : ℕ → R) (m : ℕ) :
    ∑ r ∈ range (m + 1), (-1 : R) ^ r * (T r + if r = 0 then 0 else T (r - 1)) =
      (-1) ^ m * T m := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; simp; ring

theorem derivative_shiftR {N k : ℕ} (h2 : 2 ≤ k) (hk : k ≤ N) :
    Polynomial.derivative (∑ r ∈ range k, (-1) ^ r * shiftE (hookRho N k r)) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [Polynomial.derivative_sum]
  have : ∀ r ∈ range (m + 1), Polynomial.derivative ((-1) ^ r * shiftE (hookRho N (m + 1) r)) =
      (-1) ^ r * (shiftE (hookRho N m r) + if r = 0 then 0 else shiftE (hookRho N m (r - 1))) := by
    intro r hr
    rw [Polynomial.derivative_mul, derivative_shiftE_hook (mem_range.1 hr) hk]
    simp [Polynomial.derivative_pow]
  rw [Finset.sum_congr rfl this, telescope (fun r => shiftE (hookRho N m r)) m]
  have h01 : (⟨0, by omega⟩ : Fin N) ≠ ⟨1, by omega⟩ := by simp
  rw [shiftE_eq_zero _ h01, mul_zero]
  simp only [hookRho]
  split_ifs <;> first | contradiction | omega

theorem eval_eq_of_derivative {N : ℕ} (P : Polynomial (MvPolynomial (Fin N) ℝ))
    (h : Polynomial.derivative P = 0) (b : MvPolynomial (Fin N) ℝ) : P.eval b = P.eval 0 := by
  rw [Polynomial.eq_C_of_derivative_eq_zero h]
  simp

theorem shift_invariant : ∀ (N k : ℕ) (a : ℝ), 2 ≤ k → k ≤ N →
    aeval (fun i : Fin N => (X i + C a : MvPolynomial (Fin N) ℝ)) (hookR N k) = hookR N k ∧
    aeval (fun i : Fin N => (X i + C a : MvPolynomial (Fin N) ℝ)) (detE (rho N)) = detE (rho N) := by
  intro N k a h2 hk
  constructor
  · have := eval_eq_of_derivative _ (derivative_shiftR h2 hk) (C a)
    simp only [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_neg, Polynomial.eval_one, eval_shiftE, eval_zero_shiftE] at this
    simpa [hookR, map_sum] using this
  · rw [← eval_shiftE, eval_eq_of_derivative _ (derivative_shiftE_rho N), eval_zero_shiftE]

end GlobalTheory.FlagHookShift
