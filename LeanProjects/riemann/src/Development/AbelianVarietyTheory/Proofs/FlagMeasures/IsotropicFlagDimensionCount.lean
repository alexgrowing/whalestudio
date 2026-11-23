import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SqSumEqSumSqAddTwoMulSumLt

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst

theorem finrank_le_card_of_isotropic {n : ℕ} (ε : Fin n → Bool) (V : Submodule ℂ (Fin n → ℂ))
    (hV : ∀ x ∈ V, star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x) = 0) (b : Bool) :
    Module.finrank ℂ V ≤ (univ.filter fun a => ε a = b).card := by

  let f : V →ₗ[ℂ] ({a // ε a = b} → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (Subtype.val : {a // ε a = b} → Fin n)) ∘ₗ V.subtype
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hx0 : ∀ a, ε a = b → (x : Fin n → ℂ) a = 0 := fun a ha => by
      simpa [f] using congrFun hx ⟨a, ha⟩
    have hterm : ∀ a, star ((x : Fin n → ℂ) a) * ((if ε a then (1 : ℂ) else -1) * (x : Fin n → ℂ) a)
        = (if b then (-1 : ℂ) else 1) * ((Complex.normSq ((x : Fin n → ℂ) a) : ℝ) : ℂ) := by
      intro a
      by_cases ha : ε a = b
      · simp [hx0 a ha]
      · have hb : ε a = !b := by cases h1 : ε a <;> cases b <;> simp_all
        rw [Complex.normSq_eq_conj_mul_self, hb]
        cases b <;> simp [Complex.star_def] <;> ring
    have h0 := hV x x.2
    simp only [Formalism.REAL.Jm, Matrix.mulVec_diagonal, dotProduct, Pi.star_apply, hterm,
      ← Finset.mul_sum] at h0
    have hc : (if b then (-1 : ℂ) else 1) ≠ 0 := by cases b <;> simp
    have hsum : (∑ a, Complex.normSq ((x : Fin n → ℂ) a) : ℝ) = 0 := by
      have := (mul_eq_zero.mp h0).resolve_left hc
      exact_mod_cast this
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Complex.normSq_nonneg _)).mp hsum
    ext a
    simpa using hall a (Finset.mem_univ a)
  calc Module.finrank ℂ V ≤ Module.finrank ℂ ({a // ε a = b} → ℂ) :=
        LinearMap.finrank_le_finrank_of_injective hf
    _ = Fintype.card {a // ε a = b} := Module.finrank_fintype_fun_eq_card ℂ
    _ = (univ.filter fun a => ε a = b).card := Fintype.card_subtype _

private theorem finrank_last_eq_sum_of_finrank_succ {n : ℕ} : ∀ (a : ℕ) (j : Fin a → ℕ)
    (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), W 0 = ⊥ →
    (∀ i : Fin a, Module.finrank ℂ (W i.succ) = Module.finrank ℂ (W i.castSucc) + j i) →
    Module.finrank ℂ (W (Fin.last a)) = ∑ i, j i := by
  intro a
  induction a with
  | zero =>
    intro j W h0 _
    simp [show Fin.last 0 = (0 : Fin 1) from rfl, h0]
  | succ a ih =>
    intro j W h0 hstep
    have hprev := ih (fun i => j i.castSucc) (fun i => W i.castSucc) (by simpa using h0)
      (fun i => by have hs := hstep i.castSucc; rw [Fin.succ_castSucc] at hs; exact hs)
    rw [Fin.sum_univ_castSucc, ← hprev, ← Fin.succ_last, hstep (Fin.last a)]

theorem finrank_last_eq_sum {n : ℕ} {ε : Fin n → Bool} {a : ℕ} {j : Fin a → ℕ}
    {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)} (h : IsIsoFlag ε j W) :
    Module.finrank ℂ (W (Fin.last a)) = ∑ i, j i :=
  finrank_last_eq_sum_of_finrank_succ a j W h.1 h.2.2.1

private theorem sq_sum_eq_sum_sq_add_two_mul_sum_lt' {a : ℕ} (j : Fin a → ℕ) :
    (∑ i, j i) ^ 2 = ∑ i, j i ^ 2 + 2 * ∑ i, ∑ k ∈ univ.filter (fun k => i < k), j i * j k := by
  have split : ∀ i k : Fin a, j i * j k = (if i < k then j i * j k else 0) +
      (if i = k then j i * j k else 0) + (if k < i then j i * j k else 0) := by
    intro i k
    rcases lt_trichotomy i k with h | h | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.mpr h.le]
  have hsym : ∑ i, ∑ k, (if k < i then j i * j k else 0) = ∑ i, ∑ k, (if i < k then j i * j k else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm]
  have hexp : ∑ i, ∑ k, j i * j k = ∑ i, ∑ k, ((if i < k then j i * j k else 0) +
      (if i = k then j i * j k else 0) + (if k < i then j i * j k else 0)) :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => split i k
  have hdiag : ∑ i, ∑ k, (if i = k then j i * j k else 0) = ∑ i, j i ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_ite_eq]
    simp [sq]
  rw [sq, Finset.sum_mul_sum, hexp]
  simp only [Finset.sum_add_distrib]
  rw [hsym, hdiag]
  simp only [Finset.sum_filter]
  ring

theorem flag_dims : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ (p q : ℕ), (univ.filter fun a => ε a = true).card = p → (univ.filter fun a => ε a = false).card = q → p + q = n ∧ n ^ 2 = 2 * dimN n j + ((n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2) ∧ p ^ 2 + q ^ 2 = dimN n j + ((p - ∑ i, j i) ^ 2 + (q - ∑ i, j i) ^ 2 + ∑ i, j i ^ 2) := by
  intro n ε a j W h p q hp hq
  have hpq : p + q = n := by
    rw [← hp, ← hq]
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
      (fun a => ε a = true)
    simpa using this

  have hV : ∀ x ∈ W (Fin.last a), star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x) = 0 :=
    fun x hx => h.2.2.2 x hx x hx
  have hS := finrank_last_eq_sum h
  have hSp : ∑ i, j i ≤ p := by
    rw [← hS, ← hp]; exact finrank_le_card_of_isotropic ε _ hV true
  have hSq : ∑ i, j i ≤ q := by
    rw [← hS, ← hq]; exact finrank_le_card_of_isotropic ε _ hV false
  have hsq := sq_sum_eq_sum_sq_add_two_mul_sum_lt' j
  subst hpq
  simp only [dimN]
  set S := ∑ i, j i
  set X := ∑ i, j i ^ 2
  set T := ∑ i, ∑ k ∈ univ.filter (fun k => i < k), j i * j k
  obtain ⟨P, rfl⟩ := Nat.exists_eq_add_of_le hSp
  obtain ⟨Q, rfl⟩ := Nat.exists_eq_add_of_le hSq
  have e1 : S + P + (S + Q) - 2 * S = P + Q := by omega
  have e2 : S + P - S = P := by omega
  have e3 : S + Q - S = Q := by omega
  rw [e1, e2, e3]
  refine ⟨by trivial, ?_, ?_⟩ <;> nlinarith [hsq]

end GlobalTheory.IwConst
