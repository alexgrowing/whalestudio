import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledBoxRadiiAtEntry
open ValuativeRel Matrix GlobalTheory.SplitFlip GlobalTheory.FullRankCoinv GlobalTheory.RankCoinv GlobalTheory.NormalCore

namespace GlobalTheory.BoxMove

theorem val_mul_mul_le {k : Type} [Field k] [ValuativeRel k] {a b c e : ℕ}
    (P : Matrix (Fin a) (Fin b) k) (M : Matrix (Fin b) (Fin c) k) (Q : Matrix (Fin c) (Fin e) k)
    (γ : ValueGroupWithZero k)
    (hP : ∀ i j, valuation k (P i j) ≤ 1) (hM : ∀ i j, valuation k (M i j) ≤ γ)
    (hQ : ∀ i j, valuation k (Q i j) ≤ 1) :
    ∀ i j, valuation k ((P * M * Q) i j) ≤ γ := by
  have h1 : ∀ i l, valuation k ((P * M) i l) ≤ γ := by
    intro i l
    rw [Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun m _ => ?_
    rw [map_mul]
    calc valuation k (P i m) * valuation k (M m l) ≤ 1 * γ :=
          mul_le_mul' (hP i m) (hM m l)
      _ = γ := one_mul _
  intro i j
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul]
  calc valuation k ((P * M) i l) * valuation k (Q l j) ≤ γ * 1 :=
        mul_le_mul' (h1 i l) (hQ l j)
    _ = γ := mul_one _

theorem boxmove (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n d : ℕ) (ϖ : kˣ) (g : GL (Fin n) k) (h : GL (Fin d) k)
    (hg : ∀ i j, valuation k (g.1 i j) ≤ 1) (hg' : ∀ i j, valuation k ((g⁻¹).1 i j) ≤ 1)
    (hh : ∀ i j, valuation k (h.1 i j) ≤ 1) (hh' : ∀ i j, valuation k ((h⁻¹).1 i j) ≤ 1)
    (C : Matrix (Fin n) (Fin d) k) (N : ℕ) :
    {Y : Matrix (Fin n) (Fin d) k | (g.1)ᵀ * Y * h.1 ∈ box ϖ ((g.1)ᵀ * C * h.1) (fun _ => N)} =
      box ϖ C (fun _ => N) := by
  set γ := valuation k (((ϖ ^ N : kˣ)) : k)
  have key : ∀ Y : Matrix (Fin n) (Fin d) k,
      (g.1)ᵀ * Y * h.1 - (g.1)ᵀ * C * h.1 = (g.1)ᵀ * (Y - C) * h.1 := by
    intro Y; rw [Matrix.mul_sub, Matrix.sub_mul]
  have back : ∀ Y : Matrix (Fin n) (Fin d) k,
      ((g⁻¹).1)ᵀ * ((g.1)ᵀ * (Y - C) * h.1) * (h⁻¹).1 = Y - C := by
    intro Y
    have hg1 : ((g⁻¹).1)ᵀ * (g.1)ᵀ = 1 := by
      rw [← Matrix.transpose_mul]
      simp
    have hh1 : h.1 * (h⁻¹).1 = 1 := by simp
    calc ((g⁻¹).1)ᵀ * ((g.1)ᵀ * (Y - C) * h.1) * (h⁻¹).1
        = (((g⁻¹).1)ᵀ * (g.1)ᵀ) * (Y - C) * (h.1 * (h⁻¹).1) := by
          simp only [Matrix.mul_assoc]
      _ = Y - C := by rw [hg1, hh1, Matrix.one_mul, Matrix.mul_one]
  ext Y
  simp only [Set.mem_setOf_eq, box]
  constructor
  · intro hY i j
    have hZ : ∀ i j, valuation k (((g.1)ᵀ * (Y - C) * h.1) i j) ≤ γ := by
      intro i j
      have := hY i j
      rwa [← Matrix.sub_apply, key] at this
    have := val_mul_mul_le ((g⁻¹).1)ᵀ _ (h⁻¹).1 γ (fun i j => hg' j i) hZ hh' i j
    rwa [back, Matrix.sub_apply] at this
  · intro hY i j
    rw [← Matrix.sub_apply, key]
    exact val_mul_mul_le (g.1)ᵀ (Y - C) h.1 γ (fun i j => hg j i)
      (fun i j => by rw [Matrix.sub_apply]; exact hY i j) hh i j

end GlobalTheory.BoxMove
