import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite

noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.CartGL

variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n : ℕ}

def IsUnif (p : Lˣ) : Prop := ‖(p : L)‖ < 1 ∧ ∀ x : L, x ≠ 0 → ∃ a : ℤ, ‖x‖ = ‖(p : L)‖ ^ a

theorem entry_mul {A B : Matrix (Fin n) (Fin n) L} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ i j, ‖A i j‖ ≤ a) (hB : ∀ i j, ‖B i j‖ ≤ b) (i j : Fin n) : ‖(A * B) i j‖ ≤ a * b := by
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg ha hb) fun l _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hA i l) (hB l j) (norm_nonneg _) ha

theorem entry_mul_sub_one {A B : Matrix (Fin n) (Fin n) L} {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1)
    (hA : ∀ i j, ‖(A - 1) i j‖ ≤ r) (hB : ∀ i j, ‖(B - 1) i j‖ ≤ r) (i j : Fin n) :
    ‖(A * B - 1) i j‖ ≤ r := by
  have e : A * B - 1 = (A - 1) * (B - 1) + (A - 1) + (B - 1) := by noncomm_ring
  rw [e, Matrix.add_apply, Matrix.add_apply]
  have h := entry_mul h0 h0 hA hB i j
  have h2 : r * r ≤ r := by nlinarith
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (hB i j))
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h.trans h2) (hA i j))

variable (L n) in

def congK (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) : Subgroup (GL (Fin n) L) where
  carrier := {k | ∀ i j, ‖((k : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r ∧
    ‖(((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r}
  mul_mem' := by
    intro a b ha hb i j
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]
      exact entry_mul_sub_one h0 h1 (fun i j => (ha i j).1) (fun i j => (hb i j).1) i j
    · rw [_root_.mul_inv_rev, Units.val_mul]
      exact entry_mul_sub_one h0 h1 (fun i j => (hb i j).2) (fun i j => (ha i j).2) i j
  one_mem' := by
    intro i j
    simp [h0]
  inv_mem' := by
    intro a ha i j
    simpa [and_comm] using ha i j

theorem mem_congK {r : ℝ} {h0 : 0 ≤ r} {h1 : r ≤ 1} {k : GL (Fin n) L} :
    k ∈ congK L n r h0 h1 ↔ ∀ i j, ‖((k : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r ∧
      ‖(((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r := Iff.rfl

def dPow (p : Lˣ) (a : Fin n → ℤ) : GL (Fin n) L where
  val := diagonal fun i => ((p ^ a i : Lˣ) : L)
  inv := diagonal fun i => ((p ^ (-a i) : Lˣ) : L)
  val_inv := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    rw [← Units.val_mul, _root_.zpow_neg, mul_inv_cancel, Units.val_one]
  inv_val := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    rw [← Units.val_mul, _root_.zpow_neg, inv_mul_cancel, Units.val_one]

theorem dPow_val (p : Lˣ) (a : Fin n → ℤ) :
    ((dPow p a : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = diagonal fun i => ((p ^ a i : Lˣ) : L) := rfl

theorem dPow_add (p : Lˣ) (a b : Fin n → ℤ) : (dPow p (a + b) : GL (Fin n) L) = dPow p a * dPow p b := by
  apply Units.ext
  rw [Units.val_mul, dPow_val, dPow_val, dPow_val, diagonal_mul_diagonal]
  congr 1
  funext i
  rw [Pi.add_apply, _root_.zpow_add, Units.val_mul]

theorem dPow_zero (p : Lˣ) : (dPow p (0 : Fin n → ℤ) : GL (Fin n) L) = 1 := by
  apply Units.ext
  simp [dPow_val]

def tExp (n : ℕ) (i : Fin (n + 2)) : Fin n → ℤ :=
  fun j => if (i : ℕ) = n + 1 then -1 else if (j : ℕ) < i then 1 else 0

def tGen (p : Lˣ) (i : Fin (n + 2)) : GL (Fin n) L := dPow p (tExp n i)

end GlobalTheory.CompanionTheory.CartGL
