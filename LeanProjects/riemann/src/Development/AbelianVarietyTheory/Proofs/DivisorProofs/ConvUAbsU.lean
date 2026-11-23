import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GindikinKarpelevich

noncomputable section

open MeasureTheory

namespace GlobalTheory

namespace WeylCell

def invNumU {n : ℕ} (w : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ w p.2 < w p.1).card

def partnerU {n : ℕ} (k : Fin (n / 2)) : Fin n :=
  if h : k.val + 1 < n / 2 then lo (⟨k.val + 1, h⟩ : Fin (n / 2)) else (lo k).rev

def simpleU {n : ℕ} (k : Fin (n / 2)) : Equiv.Perm (Fin n) :=
  if k.val + 1 < n / 2 then Equiv.swap (lo k) (partnerU k) * Equiv.swap (lo k).rev (partnerU k).rev
  else Equiv.swap (lo k) (lo k).rev

def actU {n : ℕ} (k : Fin (n / 2)) (α : Fin (n / 2) → ℂˣ) : Fin (n / 2) → ℂˣ :=
  if h : k.val + 1 < n / 2 then α ∘ Equiv.swap k ⟨k.val + 1, h⟩ else Function.update α k (α k)⁻¹

def rootValU {n : ℕ} (k : Fin (n / 2)) (α : Fin (n / 2) → ℂˣ) : ℂ :=
  if h : k.val + 1 < n / 2 then (α k : ℂ) / α ⟨k.val + 1, h⟩ else α k

def cSimpleU (q : ℕ) {n : ℕ} (k : Fin (n / 2)) (α : Fin (n / 2) → ℂˣ) : ℂ :=
  if h : k.val + 1 < n / 2 then cSL ((q : ℂ) ^ 2) ((α k : ℂ) / α ⟨k.val + 1, h⟩)
  else if Even n then cSL q (α k) else cSU q (α k)

def cWeylU (q : ℕ) {n : ℕ} (w : Equiv.Perm (Fin n)) (α : Fin (n / 2) → ℂˣ) : ℂ :=
  (∏ i, ∏ j with i < j ∧ w (lo j) < w (lo i), cSL ((q : ℂ) ^ 2) ((α i : ℂ) / α j)) *
    (∏ i, ∏ j with i < j ∧ w (lo j).rev < w (lo i), cSL ((q : ℂ) ^ 2) ((α i : ℂ) * α j)) *
    ∏ i with w (lo i).rev < w (lo i), if Even n then cSL q (α i) else cSU q (α i)

def ConvU {n : ℕ} (w : Equiv.Perm (Fin n)) (α : Fin (n / 2) → ℂˣ) : Prop :=
  (∀ i j, i < j → w (lo j) < w (lo i) → ‖(α i : ℂ) / α j‖ < 1) ∧
    (∀ i j, i < j → w (lo j).rev < w (lo i) → ‖(α i : ℂ) * α j‖ < 1) ∧
    ∀ i, w (lo i).rev < w (lo i) → ‖(α i : ℂ)‖ < 1

def absU {m : ℕ} (α : Fin m → ℂˣ) : Fin m → ℂˣ :=
  fun i => Units.mk0 ((‖(α i : ℂ)‖ : ℝ) : ℂ) (by simp)

theorem IsWeylRep.mul {R : Type} [CommRing R] {n : ℕ} {w v : Equiv.Perm (Fin n)} {x y : GL (Fin n) R}
    (hx : IsWeylRep w x) (hy : IsWeylRep v y) : IsWeylRep (w * v) (x * y) := by
  intro i j hij
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single (v j)]
  · rw [hx i (v j) (by simpa using hij), zero_mul]
  · intro b _ hb; rw [hy b j hb, mul_zero]
  · simp

theorem IsWeylRep.inv {R : Type} [CommRing R] {n : ℕ} {v : Equiv.Perm (Fin n)} {y : GL (Fin n) R}
    (hy : IsWeylRep v y) : IsWeylRep v⁻¹ y⁻¹ := by
  have key : ∀ i j, ((y⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i (v j) *
      (y : Matrix (Fin n) (Fin n) R) (v j) j = if i = j then 1 else 0 := by
    intro i j
    have h := congrFun (congrFun (Units.inv_mul y) i) j
    rw [Matrix.mul_apply, Finset.sum_eq_single (v j)] at h
    · rw [h, Matrix.one_apply]
    · intro b _ hb; rw [hy b j hb, mul_zero]
    · simp
  have hv : ∀ j, v (v⁻¹ j) = j := fun j => by simp
  intro i j hij
  have hu : IsUnit ((y : Matrix (Fin n) (Fin n) R) j (v⁻¹ j)) := by
    have h := key (v⁻¹ j) (v⁻¹ j)
    rw [hv, if_pos rfl] at h
    exact IsUnit.of_mul_eq_one_right _ h
  have h := key i (v⁻¹ j)
  rw [hv, if_neg hij] at h
  exact hu.mul_left_eq_zero.1 h

end WeylCell

end GlobalTheory

end
