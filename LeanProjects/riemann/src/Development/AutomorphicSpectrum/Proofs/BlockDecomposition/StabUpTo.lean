import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore

noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.CFin

abbrev Idx (r m : ℕ) : Type := Fin r ⊕ Fin m ⊕ Fin r

def frm {A : Type} {n r m : ℕ} (X : Matrix (Fin n) (Fin r) A) (Z : Matrix (Fin n) (Fin m) A)
    (Y : Matrix (Fin n) (Fin r) A) : Matrix (Fin n) (Idx r m) A :=
  Matrix.fromCols X (Matrix.fromCols Z Y)

def cnt {r : ℕ} (S : Finset (Fin r)) (i : Fin r) : ℤ := ((S.filter (· < i)).card : ℤ)

def lev {r : ℕ} (m : ℕ) (S : Finset (Fin r)) : Idx r m → ℤ
  | .inl i => cnt S i - S.card
  | .inr (.inl _) => 0
  | .inr (.inr i) => S.card - cnt S i

def wt {r : ℕ} (m : ℕ) (t : Fin r → ℝ) : Idx r m → ℝ
  | .inl i => t i
  | .inr (.inl _) => 1
  | .inr (.inr i) => (t i)⁻¹

def bd {ι A : Type} [Zero A] (b : ι → ℤ) (M : Matrix ι ι A) : Matrix ι ι A :=
  Matrix.of fun u v => if b u = b v then M u v else 0

open Classical in

def deep {r : ℕ} (t₁ : ℝ) (t : Fin r → ℝ) : Finset (Fin r) :=
  Finset.univ.filter fun j => t₁ < t j ∧ ∀ j' : Fin r, j'.val = j.val + 1 → t₁ * t j' < t j

def StabUpTo {L : Type} [CommRing L] {n r : ℕ} (X : Matrix (Fin n) (Fin r) L) (g : Matrix (Fin n) (Fin n) L)
    (j : Fin r) : Prop :=
  ∀ l : Fin r, l ≤ j → ∃ b : Fin r → L, g *ᵥ (fun a => X a l) = X *ᵥ b ∧ ∀ m : Fin r, j < m → b m = 0

theorem bd_map {ι A B : Type} [Zero A] [Zero B] (b : ι → ℤ) (φ : A → B) (h0 : φ 0 = 0) (M : Matrix ι ι A) :
    (bd b M).map φ = bd b (M.map φ) := by
  ext u v
  by_cases h : b u = b v <;> simp [bd, h, h0]

theorem bd_mul {ι A : Type} [Fintype ι] [CommRing A] {b : ι → ℤ} {M N : Matrix ι ι A}
    (hM : M.BlockTriangular b) (hN : N.BlockTriangular b) : bd b (M * N) = bd b M * bd b N := by
  ext u v
  simp only [bd, Matrix.of_apply, Matrix.mul_apply]
  by_cases h : b u = b v
  · rw [if_pos h]
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases h1 : b u = b w
    · rw [if_pos h1, if_pos (h1.symm.trans h)]
    · rw [if_neg h1]
      rcases lt_or_gt_of_ne h1 with h2 | h2
      · rw [show N w v = 0 from hN (by omega), mul_zero, zero_mul]
      · rw [show M u w = 0 from hM h2, zero_mul, zero_mul]
  · rw [if_neg h]
    refine (Finset.sum_eq_zero fun w _ => ?_).symm
    by_cases h1 : b u = b w
    · rw [if_neg (fun e => h (h1.trans e)), mul_zero]
    · rw [if_neg h1, zero_mul]

end GlobalTheory.CompanionTheory.CFin

end
