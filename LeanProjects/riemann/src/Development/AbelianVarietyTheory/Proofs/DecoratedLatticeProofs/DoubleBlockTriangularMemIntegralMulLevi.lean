import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.PClassAlg

variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}

theorem shape_aX (hp : 1 ≤ p) (B : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
    (h1 : B.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))))
    (h2 : B.BlockTriangular (fun r => OrderDual.toDual (lev p r))) (l : Fin c) (y : n) :
    B (Sum.inr l) (Sum.inl y) = 0 := by
  by_cases h : l.val + 1 < p
  · apply h2
    show OrderDual.toDual (lev p (Sum.inl y : n ⊕ Fin c)) < OrderDual.toDual (lev p (Sum.inr l : n ⊕ Fin c))
    simp only [lev, Sum.elim_inl, Sum.elim_inr, OrderDual.toDual_lt_toDual]; omega
  · apply h1; simp only [Sum.elim_inl, Sum.elim_inr]; omega

theorem shape_aa (B : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
    (h1 : B.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))))
    (h2 : B.BlockTriangular (fun r => OrderDual.toDual (lev p r))) (i j : Fin c) (hij : i ≠ j) :
    B (Sum.inr i) (Sum.inr j) = 0 := by
  have : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne this with h | h
  · apply h2
    show OrderDual.toDual (lev p (Sum.inr j : n ⊕ Fin c)) < OrderDual.toDual (lev p (Sum.inr i : n ⊕ Fin c))
    simp only [lev, Sum.elim_inr, OrderDual.toDual_lt_toDual]; omega
  · apply h1; simp only [Sum.elim_inr]; omega

theorem shape_Xa (B : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
    (h1 : B.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))))
    (h2 : B.BlockTriangular (fun r => OrderDual.toDual (lev p r))) (x : n) (i : Fin c) (hi : i.val + 1 ≠ p) :
    B (Sum.inl x) (Sum.inr i) = 0 := by
  rcases Nat.lt_or_gt_of_ne hi with h | h
  · apply h1; simp only [Sum.elim_inl, Sum.elim_inr]; omega
  · apply h2
    show OrderDual.toDual (lev p (Sum.inr i : n ⊕ Fin c)) < OrderDual.toDual (lev p (Sum.inl x : n ⊕ Fin c))
    simp only [lev, Sum.elim_inl, Sum.elim_inr, OrderDual.toDual_lt_toDual]; omega

theorem eq_fromBlocks (hp : 1 ≤ p) (B : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
    (h1 : B.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))))
    (h2 : B.BlockTriangular (fun r => OrderDual.toDual (lev p r))) :
    B = fromBlocks (toBlocks₁₁ B) (toBlocks₁₂ B) 0 (toBlocks₂₂ B) := by
  conv_lhs => rw [← fromBlocks_toBlocks B]
  congr 1
  ext l y; exact shape_aX hp B h1 h2 l y

theorem diag_block (B : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
    (h1 : B.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))))
    (h2 : B.BlockTriangular (fun r => OrderDual.toDual (lev p r))) :
    toBlocks₂₂ B = diagonal fun i => B (Sum.inr i) (Sum.inr i) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [toBlocks₂₂]
  · simp [toBlocks₂₂, diagonal_apply_ne _ h, shape_aa B h1 h2 i j h]

end GlobalTheory.PClassAlg

namespace GlobalTheory.PClassAlg

theorem blockDiag_mem_KO : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ) (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ), 1 ≤ p → p ≤ c → ∀ (A : GL (n ⊕ Fin c) k), A.val.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))) → A.val.BlockTriangular (fun r => OrderDual.toDual (lev p r)) → (A⁻¹).val.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))) → (A⁻¹).val.BlockTriangular (fun r => OrderDual.toDual (lev p r)) → (∀ i : Fin c, A.val (Sum.inr i) (Sum.inr i) * (ϖ : k) ^ (i.val + 1) ∈ 𝒪[k] ∧ (A⁻¹).val (Sum.inr i) (Sum.inr i) * ((ϖ : k) ^ (i.val + 1))⁻¹ ∈ 𝒪[k]) → (∀ i : Fin c, i.val + 1 = p → ∀ x : n, A.val (Sum.inl x) (Sum.inr i) * (ϖ : k) ^ (i.val + 1) ∈ 𝒪[k]) → ∃ γ : GL n k, A * embX c γ * embA n (GlobalTheory.SplitFlip.diagGL fun i : Fin c => ϖ ^ (i.val + 1)) ∈ KO k (n ⊕ Fin c) := by
  intro k _ _ _ _ ϖ n _ _ c p hp hpc A hA1 hA2 hB1 hB2 hD hE
  have eA := eq_fromBlocks hp _ hA1 hA2
  have eB := eq_fromBlocks hp _ hB1 hB2
  have dA := diag_block _ hA1 hA2
  have dB := diag_block _ hB1 hB2
  have sXa := shape_Xa _ hA1 hA2
  set P := toBlocks₁₁ A.val
  set Q := toBlocks₁₂ A.val
  set S := toBlocks₂₂ A.val
  set P' := toBlocks₁₁ (A⁻¹).val
  set Q' := toBlocks₁₂ (A⁻¹).val
  set S' := toBlocks₂₂ (A⁻¹).val
  have hAB : A.val * (A⁻¹).val = 1 := Units.mul_inv A
  have hBA : (A⁻¹).val * A.val = 1 := Units.inv_mul A
  rw [eA, eB, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj] at hAB hBA
  simp only [Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add] at hAB hBA
  obtain ⟨hPP', hPQ, -, -⟩ := hAB
  obtain ⟨hP'P, -, -, -⟩ := hBA
  let γ : GL n k := ⟨P', P, hP'P, hPP'⟩
  have hpow : ∀ i : Fin c, (((ϖ ^ (i.val + 1) : kˣ)) : k) = (ϖ : k) ^ (i.val + 1) := fun i => by simp
  have hne : ∀ i : Fin c, (ϖ : k) ^ (i.val + 1) ≠ 0 := fun i => pow_ne_zero _ ϖ.ne_zero
  refine ⟨γ, (GlobalTheory.SplitFlip.mem_KO_iff _).2 ⟨?_, ?_⟩⟩
  · have hM : (A * embX c γ * embA n (GlobalTheory.SplitFlip.diagGL fun i : Fin c => ϖ ^ (i.val + 1))).val =
        fromBlocks (P * P') (Q * diagonal fun i : Fin c => (ϖ : k) ^ (i.val + 1)) 0
          (S * diagonal fun i : Fin c => (ϖ : k) ^ (i.val + 1)) := by
      rw [Units.val_mul, Units.val_mul, eA]
      show fromBlocks P Q 0 S * fromBlocks P' 0 0 1 * fromBlocks 1 0 0 (GlobalTheory.SplitFlip.diagGL fun i : Fin c => ϖ ^ (i.val + 1)).val = _
      simp [fromBlocks_multiply, hpow]
    rw [hM, hPP']
    rintro (x | l) (y | i)
    · simp only [fromBlocks_apply₁₁, one_apply]; split_ifs <;> simp
    · simp only [fromBlocks_apply₁₂, mul_diagonal]
      by_cases h : i.val + 1 = p
      · exact hE i h x
      · simp [Q, toBlocks₁₂, sXa x i h]
    · simp
    · simp only [fromBlocks_apply₂₂, mul_diagonal, dA]
      by_cases h : l = i
      · subst h; simpa using (hD l).1
      · simp [diagonal_apply_ne _ h]

  · have hM : ((A * embX c γ * embA n (GlobalTheory.SplitFlip.diagGL fun i : Fin c => ϖ ^ (i.val + 1)))⁻¹).val =
        fromBlocks (P * P') (P * Q') 0
          ((diagonal fun i : Fin c => ((ϖ : k) ^ (i.val + 1))⁻¹) * S') := by
      rw [_root_.mul_inv_rev, _root_.mul_inv_rev, ← map_inv, ← map_inv, Units.val_mul, Units.val_mul, eB]
      show fromBlocks 1 0 0 ((GlobalTheory.SplitFlip.diagGL fun i : Fin c => ϖ ^ (i.val + 1))⁻¹).val *
        (fromBlocks P 0 0 1 * fromBlocks P' Q' 0 S') = _
      have : ((GlobalTheory.SplitFlip.diagGL fun i : Fin c => ϖ ^ (i.val + 1))⁻¹).val =
          diagonal fun i : Fin c => ((ϖ : k) ^ (i.val + 1))⁻¹ := by
        ext i j; simp [GlobalTheory.SplitFlip.diagGL, diagonal_apply]
      rw [this]
      simp [fromBlocks_multiply]
    have hPQ' : P * Q' = -(Q * S') := eq_neg_of_add_eq_zero_left hPQ
    rw [hM, hPP', hPQ', dB]
    rintro (x | l) (y | i)
    · simp only [fromBlocks_apply₁₁, one_apply]; split_ifs <;> simp
    · simp only [fromBlocks_apply₁₂, Matrix.neg_apply, mul_diagonal]
      by_cases h : i.val + 1 = p
      · have e : Q x i * (A⁻¹).val (Sum.inr i) (Sum.inr i) =
            (A.val (Sum.inl x) (Sum.inr i) * (ϖ : k) ^ (i.val + 1)) *
              ((A⁻¹).val (Sum.inr i) (Sum.inr i) * ((ϖ : k) ^ (i.val + 1))⁻¹) := by
          have := hne i
          simp only [Q, toBlocks₁₂, of_apply]
          field_simp
        rw [e]
        exact neg_mem (mul_mem (hE i h x) (hD i).2)
      · simp [Q, toBlocks₁₂, sXa x i h]
    · simp
    · simp only [fromBlocks_apply₂₂, diagonal_mul_diagonal, diagonal_apply]
      split_ifs with h
      · subst h; rw [mul_comm]; exact (hD l).2
      · exact zero_mem _

end GlobalTheory.PClassAlg
