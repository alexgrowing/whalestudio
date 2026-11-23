import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad
open Matrix GlobalTheory.TorFin

namespace GlobalTheory.CapelliNext

open Finset

variable {A : Type} [Ring A] [Algebra ℂ A]

def shiftCoeff (d : ℕ) (p q : A) (c : ℕ → A) : ℕ → A :=
  fun i => (Nat.casesOn i 0 (fun j => p * c j) : A) + (if i < d + 1 then q * c i else 0)

theorem affine_mul_eq (d : ℕ) (p q : A) (c : ℕ → A) (u : ℂ) :
    (u • p + q) * (∑ i ∈ range (d + 1), u ^ i • c i)
      = ∑ i ∈ range (d + 1 + 1), u ^ i • shiftCoeff d p q c i := by
  unfold shiftCoeff
  simp only [smul_add, sum_add_distrib, add_mul]
  congr 1
  · rw [sum_range_succ' _ (d + 1), mul_sum]
    simp only [Nat.rec_zero, smul_zero, add_zero]
    refine sum_congr rfl fun i _ => ?_
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, pow_succ]
  · rw [sum_range_succ _ (d + 1), mul_sum]
    simp only [lt_irrefl, if_false, smul_zero, add_zero]
    refine sum_congr rfl fun i hi => ?_
    rw [if_pos (mem_range.mp hi), mul_smul_comm]

theorem prod_affine_two_top (t : ℕ) (p : Fin (t + 1) → ℂ) (q : Fin (t + 1) → A) :
    ∃ c : ℕ → A, c (t + 1) = (∏ k, p k) • (1 : A) ∧
      c t = ∑ k, (∏ j, (if j = k then (1 : ℂ) else p j)) • q k ∧
      ∀ u : ℂ, (List.ofFn fun k => (u * p k) • (1 : A) + q k).prod
        = ∑ i ∈ range (t + 1 + 1), u ^ i • c i := by
  induction t with
  | zero =>
    let c : ℕ → A := fun i => if i = 0 then q 0 else if i = 1 then (p 0) • (1 : A) else 0
    refine ⟨c, ?_, ?_, fun u => ?_⟩
    · simp [c]
    · simp [c]
    · simp [c, sum_range_succ, add_comm]
      rw [mul_smul]
  | succ t ih =>
    obtain ⟨c, hc1, hc0, hc⟩ := ih (fun k => p k.succ) (fun k => q k.succ)
    refine ⟨shiftCoeff (t + 1) (p 0 • (1 : A)) (q 0) c, ?_, ?_, fun u => ?_⟩
    · simp only [shiftCoeff, lt_irrefl, if_false, add_zero]
      rw [hc1, smul_one_mul, smul_smul, ← Fin.prod_univ_succ]
    · simp only [shiftCoeff, lt_add_iff_pos_right, Nat.lt_add_one, if_true]
      rw [hc0, hc1, smul_one_mul, mul_smul_comm, mul_one, smul_sum, add_comm]
      conv_rhs => rw [Fin.sum_univ_succ]
      congr 1
      · simp [Fin.prod_univ_succ, smul_mul_assoc]
      · refine sum_congr rfl fun k _ => ?_
        simp [Fin.prod_univ_succ, Fin.succ_ne_zero, smul_smul, (Fin.succ_ne_zero _).symm]
    · rw [List.ofFn_succ, List.prod_cons, hc u]
      have : (u * p 0) • (1 : A) + q 0 = u • (p 0 • (1 : A)) + q 0 := by rw [smul_smul]
      rw [this, affine_mul_eq]

end GlobalTheory.CapelliNext

namespace GlobalTheory.CapelliNext
open Finset

theorem qdet_shift_next_coeff : ∀ (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A) (s : ℂ), ∃ (c : ℕ → A) (t : ℂ),
    c (m + 1) = 1 ∧ c m = ∑ i, E i i + t • (1 : A) ∧
      ∀ u : ℂ, Formalism.REAL.qdet E (u - s) = ∑ k ∈ Finset.range (m + 1 + 1), u ^ k • c k := by
  intro A _ _ m E s
  have h : ∀ σ : Equiv.Perm (Fin (m + 1)), ∃ c : ℕ → A,
      c (m + 1) = (∏ k, (if σ k = k then (1 : ℂ) else 0)) • (1 : A) ∧
      c m = ∑ k, (∏ j, (if j = k then (1 : ℂ) else (if σ j = j then (1 : ℂ) else 0))) •
        ((if σ k = k then algebraMap ℂ A (-s - ((k : ℕ) : ℂ)) else 0) + E (σ k) k) ∧
      ∀ u : ℂ, (List.ofFn fun k : Fin (m + 1) => Formalism.REAL.Tm E (u - s - ((k : ℕ) : ℂ)) (id (σ k)) (id k)).prod
        = ∑ i ∈ range (m + 1 + 1), u ^ i • c i := by
    intro σ
    obtain ⟨c, hc1, hc0, hc⟩ := prod_affine_two_top m (fun k => if σ k = k then (1 : ℂ) else 0)
      (fun k => (if σ k = k then algebraMap ℂ A (-s - ((k : ℕ) : ℂ)) else 0) + E (σ k) k)
    refine ⟨c, hc1, hc0, fun u => ?_⟩
    rw [← hc u]
    congr 2
    funext k
    unfold Formalism.REAL.Tm
    simp only [id]
    split_ifs with hk
    · rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, ← add_assoc, ← add_smul]
      congr 2
      ring
    · simp
  choose c hc1 hc0 hc using h
  refine ⟨fun i => ∑ σ : Equiv.Perm (Fin (m + 1)), ((Equiv.Perm.sign σ : ℤ) : A) * c σ i,
    ∑ k : Fin (m + 1), (-s - ((k : ℕ) : ℂ)), ?_, ?_, fun u => ?_⟩
  · simp only
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin (m + 1)))]
    · rw [hc1 1]
      simp
    · intro σ _ hσ
      obtain ⟨k, hk⟩ : ∃ k, σ k ≠ k := by
        by_contra hne
        push_neg at hne
        exact hσ (Equiv.ext hne)
      rw [hc1 σ, Finset.prod_eq_zero (mem_univ k) (if_neg hk), zero_smul, mul_zero]
    · intro h1
      exact absurd (mem_univ _) h1
  · simp only
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin (m + 1)))]
    · rw [hc0 1]
      simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul, Equiv.Perm.coe_one,
        id_eq, if_true, ite_self, prod_const_one, one_smul]
      rw [sum_add_distrib, add_comm]
      congr 1
      simp only [Algebra.algebraMap_eq_smul_one, ← sum_smul]
    · intro σ _ hσ
      obtain ⟨k₀, hk₀⟩ : ∃ k, σ k ≠ k := by
        by_contra hne
        push_neg at hne
        exact hσ (Equiv.ext hne)
      rw [hc0 σ]
      have hz : ∀ k, (∏ j, (if j = k then (1 : ℂ) else (if σ j = j then (1 : ℂ) else 0))) = 0 := by
        intro k
        by_cases hk : σ k = k
        · refine Finset.prod_eq_zero (mem_univ k₀) ?_
          have : k₀ ≠ k := fun e => hk₀ (e ▸ hk)
          simp [this, hk₀]
        · refine Finset.prod_eq_zero (mem_univ (σ k)) ?_
          have h2 : σ (σ k) ≠ σ k := fun e => hk (σ.injective e)
          simp [hk, h2]
      simp [hz]
    · intro h1
      exact absurd (mem_univ _) h1
  · unfold Formalism.REAL.qdet Formalism.REAL.qminor
    rw [Finset.sum_congr rfl fun σ _ => by rw [hc σ u]]
    simp_rw [mul_sum, mul_smul_comm]
    rw [Finset.sum_comm]
    simp_rw [← smul_sum]

end GlobalTheory.CapelliNext
