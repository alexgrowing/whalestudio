import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledBoxRadiiAtEntry

open ValuativeRel Matrix GlobalTheory.SplitFlip GlobalTheory.FullRankCoinv GlobalTheory.RankCoinv GlobalTheory.NormalCore

namespace GlobalTheory.UnitScaleBox

theorem scale_mem_box_iff {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n d : ℕ} (ϖ : kˣ) (p : Matrix (Fin n) (Fin d) k) (N : ℕ)
    (c : Fin n → Fin d → k) (hc : ∀ i j, valuation k (c i j) = 1) (hp : ∀ i j, c i j * p i j = p i j)
    (Y Z : Matrix (Fin n) (Fin d) k) (hZ : ∀ i j, Z i j = c i j * Y i j) :
    Z ∈ box ϖ p (fun _ => N) ↔ Y ∈ box ϖ p (fun _ => N) := by
  simp only [box, Set.mem_setOf_eq]
  refine forall₂_congr fun i j => ?_
  have h : Z i j - p i j = c i j * (Y i j - p i j) := by rw [hZ, mul_sub, hp]
  rw [h, map_mul, hc, one_mul]

theorem val_update {k : Type} [Field k] [ValuativeRel k] {m : ℕ} (i₀ : Fin m) (t : k) (ht : valuation k t = 1)
    (i : Fin m) : valuation k (Function.update (1 : Fin m → k) i₀ t i) = 1 := by
  by_cases h : i = i₀
  · subst h; simp [ht]
  · simp [Function.update_apply, h]

theorem box_unit_scale : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n d : ℕ) (i₀ : Fin n) (j₀ : Fin d) (ϖ u : kˣ) (p₁ p₂ : Matrix (Fin n) (Fin d) k) (N : ℕ),
    valuation k (u : k) = 1 → (∀ j, p₁ i₀ j = if j = j₀ then 1 else 0) → (∀ i, i ≠ i₀ → p₁ i j₀ = 0) →
    (∀ i, p₂ i j₀ = 0) →
    {Y : Matrix (Fin n) (Fin d) k | ((dgl i₀ u).1)ᵀ * Y * (dgl j₀ u⁻¹).1 ∈ box ϖ p₁ (fun _ => N)} =
        box ϖ p₁ (fun _ => N) ∧
      {Y : Matrix (Fin n) (Fin d) k | Y * (dgl j₀ u⁻¹).1 ∈ box ϖ p₂ (fun _ => N)} = box ϖ p₂ (fun _ => N) := by
  intro k _ _ _ _ n d i₀ j₀ ϖ u p₁ p₂ N hu h1 h1' h2
  have hu' : valuation k (((u⁻¹ : kˣ) : k)) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
  set f : Fin n → k := Function.update (1 : Fin n → k) i₀ (u : k) with hf
  set g : Fin d → k := Function.update (1 : Fin d → k) j₀ ((u⁻¹ : kˣ) : k) with hg
  have hfv : ∀ i, valuation k (f i) = 1 := val_update i₀ _ hu
  have hgv : ∀ j, valuation k (g j) = 1 := val_update j₀ _ hu'
  constructor
  · ext Y
    simp only [Set.mem_setOf_eq]
    refine scale_mem_box_iff ϖ p₁ N (fun i j => f i * g j) (fun i j => by rw [map_mul, hfv, hgv, one_mul])
      (fun i j => ?_) Y _ (fun i j => ?_)
    · by_cases hi : i = i₀ <;> by_cases hj : j = j₀
      · subst hi hj; simp [hf, hg]
      · subst hi; simp [h1 j, hj]
      · subst hj; simp [h1' i hi]
      · simp [hf, hg, Function.update_apply, hi, hj]
    · rw [dgl_val, dgl_val, diagonal_transpose, mul_diagonal, diagonal_mul]
      ring
  · ext Y
    simp only [Set.mem_setOf_eq]
    refine scale_mem_box_iff ϖ p₂ N (fun _ j => g j) (fun i j => hgv j) (fun i j => ?_) Y _ (fun i j => ?_)
    · by_cases hj : j = j₀
      · subst hj; simp [h2 i]
      · simp [hg, Function.update_apply, hj]
    · rw [dgl_val, mul_diagonal]
      ring

end GlobalTheory.UnitScaleBox
