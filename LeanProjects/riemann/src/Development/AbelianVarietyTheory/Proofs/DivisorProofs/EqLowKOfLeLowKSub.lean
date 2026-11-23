import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothReal
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemUJsetOfKset

open Matrix Finset Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory.LowHW

theorem height_root {n : ℕ} (a b : Fin n) :
    ∑ i : Fin n, ((i : ℕ) : ℝ) * Formalism.REAL.root a b i = ((a : ℕ) : ℝ) - ((b : ℕ) : ℝ) := by
  simp [Formalism.REAL.root, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]

theorem height_sum {n : ℕ} (c : Fin n → Fin n → ℕ) :
    ∑ i : Fin n, ((i : ℕ) : ℝ) * (∑ a, ∑ b, (c a b : ℝ) • Formalism.REAL.root a b) i
      = ∑ a, ∑ b, (c a b : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) := by
  simp only [← height_root, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => by ring

theorem cdom_antisymm {n : ℕ} {ε : Fin n → Bool} {μ Λ : Fin n → ℝ} (h1 : CDom ε μ Λ) (h2 : CDom ε Λ μ) :
    μ = Λ := by
  obtain ⟨c, hc, e1⟩ := h1
  obtain ⟨d, hd, e2⟩ := h2
  have key : ∀ (c : Fin n → Fin n → ℕ), (∀ a b, c a b ≠ 0 → a < b ∧ ε a = ε b) → ∀ a b : Fin n,
      (c a b : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) ≤ -(c a b : ℝ) := by
    intro c hc a b
    by_cases h : c a b = 0
    · simp [h]
    · have h3 : (a : ℕ) + 1 ≤ b := (hc a b h).1
      have h4 : ((a : ℕ) : ℝ) + 1 ≤ ((b : ℕ) : ℝ) := by exact_mod_cast h3
      have h5 : (0 : ℝ) ≤ c a b := Nat.cast_nonneg _
      nlinarith
  have hs1 := height_sum c
  have hs2 := height_sum d
  rw [← e1] at hs1
  rw [← e2] at hs2
  have hz : ∑ i : Fin n, ((i : ℕ) : ℝ) * (Λ - μ) i + ∑ i : Fin n, ((i : ℕ) : ℝ) * (μ - Λ) i = 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun i _ => by simp only [Pi.sub_apply]; ring
  have l1 : ∑ a, ∑ b, (c a b : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) ≤ ∑ a, ∑ b, -(c a b : ℝ) :=
    Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => key c hc a b
  have l2 : ∑ a, ∑ b, (d a b : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) ≤ 0 :=
    Finset.sum_nonpos fun a _ => Finset.sum_nonpos fun b _ =>
      (key d hd a b).trans (neg_nonpos.2 (Nat.cast_nonneg _))
  simp only [Finset.sum_neg_distrib] at l1
  have l3 : ∑ a, ∑ b, (c a b : ℝ) ≤ 0 := by linarith
  have hc0 : ∀ a b, (c a b : ℝ) = 0 := by
    intro a b
    refine le_antisymm (le_trans ?_ l3) (Nat.cast_nonneg _)
    calc (c a b : ℝ) ≤ ∑ b, (c a b : ℝ) :=
          Finset.single_le_sum (f := fun b => (c a b : ℝ)) (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ b)
      _ ≤ _ := Finset.single_le_sum (f := fun a => ∑ b, (c a b : ℝ))
          (fun _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ a)
  simp only [hc0, zero_smul, Finset.sum_const_zero] at e1
  exact (sub_eq_zero.1 e1).symm

end GlobalTheory.LowHW
