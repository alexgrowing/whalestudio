import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemShellUIffDepth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapLtSwapIffOfAddTwo
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

noncomputable section

namespace GlobalTheory.WeylCell.WeylUnipotentShell

section BlockKeep

variable {R : Type} [CommRing R] {n : ℕ}

def blockKeep (a b : Fin n) (A : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  fun i j => if (a ≤ i ∧ i ≤ b) ∧ (a ≤ j ∧ j ≤ b) then A i j else (1 : Matrix (Fin n) (Fin n) R) i j

theorem blockKeep_one (a b : Fin n) : blockKeep a b (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  ext i j; unfold blockKeep; split_ifs <;> rfl

theorem blockKeep_mul (a b : Fin n) (A B : Matrix (Fin n) (Fin n) R) (hA : ∀ i j, j < i → A i j = 0)
    (hB : ∀ i j, j < i → B i j = 0) : blockKeep a b (A * B) = blockKeep a b A * blockKeep a b B := by
  ext i j
  by_cases hi : a ≤ i ∧ i ≤ b
  · by_cases hj : a ≤ j ∧ j ≤ b
    · simp only [blockKeep, Matrix.mul_apply, if_pos (And.intro hi hj)]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk : a ≤ k ∧ k ≤ b
      · rw [if_pos ⟨hi, hk⟩, if_pos ⟨hk, hj⟩]
      · rw [if_neg (fun h => hk h.2), Matrix.one_apply_ne (by rintro rfl; exact hk hi), zero_mul]
        rcases not_and_or.1 hk with h | h
        · rw [hA i k (lt_of_lt_of_le (not_le.1 h) hi.1), zero_mul]
        · rw [hB k j (lt_of_le_of_lt hj.2 (not_le.1 h)), mul_zero]
    · have hcol : ∀ k, blockKeep a b B k j = (1 : Matrix (Fin n) (Fin n) R) k j := fun k => if_neg (fun h => hj h.2)
      rw [Matrix.mul_apply]
      simp only [hcol, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      simp only [blockKeep, hi, hj, and_false, if_false, true_and, Matrix.one_apply]
  · have hrow : ∀ k, blockKeep a b A i k = (1 : Matrix (Fin n) (Fin n) R) i k := fun k => if_neg (fun h => hi h.1)
    rw [Matrix.mul_apply]
    simp only [hrow, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simp only [blockKeep, hi, false_and, if_false, Matrix.one_apply]

end BlockKeep

section Keep

variable {L : Type} [Field L] {n : ℕ}

def blockKeepGL (a b : Fin n) (g : GL (Fin n) L) (hg : g ∈ unipB L (Fin n)) : GL (Fin n) L where
  val := blockKeep a b (g : Matrix (Fin n) (Fin n) L)
  inv := blockKeep a b ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
  val_inv := by
    rw [← blockKeep_mul a b _ _ ((mem_unipB L).1 hg).1 ((mem_unipB L).1 (inv_mem hg)).1, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, blockKeep_one]
  inv_val := by
    rw [← blockKeep_mul a b _ _ ((mem_unipB L).1 (inv_mem hg)).1 ((mem_unipB L).1 hg).1, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, blockKeep_one]

theorem blockKeepGL_mem_GU [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} (a : Fin n) (g : GL (Fin n) L)
    (hg : g ∈ unipB L (Fin n)) (hG : g ∈ GU σ n) : blockKeepGL a a.rev g hg ∈ GU σ n := by
  rw [LGrp.mem_GU_iff] at hG ⊢
  intro i j
  show blockKeep a a.rev ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j =
    σ (blockKeep a a.rev (g : Matrix (Fin n) (Fin n) L) j.rev i.rev)
  have key : ∀ i : Fin n, (a ≤ i.rev ∧ i.rev ≤ a.rev) ↔ (a ≤ i ∧ i ≤ a.rev) := by
    intro i
    have := i.isLt
    have := a.isLt
    simp only [Fin.le_iff_val_le_val, Fin.val_rev]
    omega
  unfold blockKeep
  simp only [key]
  by_cases h : (a ≤ i ∧ i ≤ a.rev) ∧ (a ≤ j ∧ j ≤ a.rev)
  · rw [if_pos h, if_pos h.symm, hG]
  · rw [if_neg h, if_neg (fun h' => h h'.symm), Matrix.one_apply, Matrix.one_apply, apply_ite σ, map_one, map_zero]
    simp only [Fin.rev_inj, eq_comm (a := j)]

theorem blockKeep_eq_self (a b : Fin n) (A : Matrix (Fin n) (Fin n) L) (h1 : ∀ i j, j < i → A i j = 0)
    (h2 : ∀ i, A i i = 1) (h3 : ∀ i j, i < j → (i < a ∨ b < j) → A i j = 0) : blockKeep a b A = A := by
  ext i j
  unfold blockKeep
  split_ifs with h
  · rfl
  · rcases lt_trichotomy i j with hij | rfl | hij
    · rw [Matrix.one_apply_ne hij.ne, h3 i j hij]
      by_contra hc
      rw [not_or, not_lt, not_lt] at hc
      exact h ⟨⟨hc.1, hij.le.trans hc.2⟩, hc.1.trans hij.le, hc.2⟩
    · rw [Matrix.one_apply_eq, h2]
    · rw [Matrix.one_apply_ne hij.ne', h1 i j hij]

end Keep

end GlobalTheory.WeylCell.WeylUnipotentShell
