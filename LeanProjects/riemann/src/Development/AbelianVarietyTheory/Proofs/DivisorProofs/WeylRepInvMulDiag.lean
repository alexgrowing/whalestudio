import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GindikinKarpelevich

open GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.WeylCell

namespace GlobalTheory.GKFactor

variable {k : Type} [Field k] {n : ℕ}

local notation "M" x:max => ((x : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)

theorem weylRep_inv_mul_diag {w : Equiv.Perm (Fin n)} {x : GL (Fin n) k} (hx : IsWeylRep w x) (p : Fin n) :
    (M x⁻¹) p (w p) * (M x) (w p) p = 1 := by
  have h : (M (x⁻¹ * x)) p p = (M (1 : GL (Fin n) k)) p p := by rw [inv_mul_cancel]
  rw [Units.val_mul, Matrix.mul_apply, Units.val_one, Matrix.one_apply_eq] at h
  rwa [Finset.sum_eq_single (w p) (fun b _ hb => by rw [hx b p hb, mul_zero]) (by simp)] at h

theorem weylRep_mul_inv_diag {w : Equiv.Perm (Fin n)} {x : GL (Fin n) k} (hx : IsWeylRep w x) (p : Fin n) :
    (M x) (w p) p * (M x⁻¹) p (w p) = 1 := by
  have h : (M (x * x⁻¹)) (w p) (w p) = (M (1 : GL (Fin n) k)) (w p) (w p) := by rw [mul_inv_cancel]
  rw [Units.val_mul, Matrix.mul_apply, Units.val_one, Matrix.one_apply_eq] at h
  rwa [Finset.sum_eq_single p (fun b _ hb => by
      rw [hx (w p) b (fun e => hb (w.injective e).symm), zero_mul]) (by simp)] at h

theorem weylRep_inv {w : Equiv.Perm (Fin n)} {x : GL (Fin n) k} (hx : IsWeylRep w x) : IsWeylRep w⁻¹ x⁻¹ := by
  intro p a hpa
  have hne : (M x) a (w⁻¹ a) ≠ 0 := by
    intro h0
    have := weylRep_mul_inv_diag hx (w⁻¹ a)
    rw [show w (w⁻¹ a) = a by simp] at this
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  have h : (M (x⁻¹ * x)) p (w⁻¹ a) = (M (1 : GL (Fin n) k)) p (w⁻¹ a) := by rw [inv_mul_cancel]
  rw [Units.val_mul, Matrix.mul_apply, Units.val_one, Matrix.one_apply_ne hpa] at h
  rw [Finset.sum_eq_single a (fun b _ hb => by
      rw [hx b (w⁻¹ a) (by simpa using hb), mul_zero]) (by simp)] at h
  exact (mul_eq_zero.1 h).resolve_right hne

theorem weylRep_conj_apply {w : Equiv.Perm (Fin n)} {x : GL (Fin n) k} (hx : IsWeylRep w x) (u : GL (Fin n) k)
    (p q : Fin n) : (M (x⁻¹ * u * x)) p q = (M x⁻¹) p (w p) * (M u) (w p) (w q) * (M x) (w q) q := by
  have hi := weylRep_inv hx
  rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single (w q)
    (fun b _ hb => by rw [hx b q hb, mul_zero]) (by simp), Matrix.mul_apply,
    Finset.sum_eq_single (w p) (fun b _ hb => by rw [hi p b (fun e => hb (by rw [e]; simp)), zero_mul]) (by simp)]

theorem mem_cell_iff {w : Equiv.Perm (Fin n)} {x : GL (Fin n) k} (hx : IsWeylRep w x) (u : GL (Fin n) k) :
    u ∈ cell x ↔ u ∈ unipB k (Fin n) ∧ ∀ a b, a < b → w⁻¹ a < w⁻¹ b → (M u) a b = 0 := by
  rw [mem_cell, mem_unipBLower]
  refine and_congr_right fun hu => ?_
  rw [mem_unipB] at hu
  constructor
  · rintro ⟨hl, -⟩ a b hab hw
    have h := hl _ _ hw
    rw [weylRep_conj_apply hx, show w (w⁻¹ a) = a by simp, show w (w⁻¹ b) = b by simp] at h
    have h1 := weylRep_inv_mul_diag hx (w⁻¹ a)
    have h2 := weylRep_mul_inv_diag hx (w⁻¹ b)
    rw [show w (w⁻¹ a) = a by simp] at h1
    rw [show w (w⁻¹ b) = b by simp] at h2
    rcases mul_eq_zero.1 h with h | h
    · rcases mul_eq_zero.1 h with h | h
      · rw [h, zero_mul] at h1; exact absurd h1 zero_ne_one
      · exact h
    · rw [h, zero_mul] at h2; exact absurd h2 zero_ne_one
  · intro h
    refine ⟨fun p q hpq => ?_, fun p => ?_⟩
    · rw [weylRep_conj_apply hx]
      rcases lt_or_gt_of_ne (fun e : w p = w q => hpq.ne (w.injective e)) with hl | hl
      · rw [h _ _ hl (by simpa using hpq), mul_zero, zero_mul]
      · rw [hu.1 _ _ hl, mul_zero, zero_mul]
    · rw [weylRep_conj_apply hx, hu.2, mul_one, weylRep_inv_mul_diag hx]

end GlobalTheory.GKFactor
