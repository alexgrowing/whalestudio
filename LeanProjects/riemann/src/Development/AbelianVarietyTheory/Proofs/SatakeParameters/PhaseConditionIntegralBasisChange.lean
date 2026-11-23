import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntMat

namespace GlobalTheory

open Matrix in

theorem phaseCondition_basisChange : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (δ : L)
    (n n' : ℕ) (A : Matrix (Fin n) (Fin n) L) (ψ : AddChar L ℂ)
    (P : Matrix (Fin n') (Fin n') L) (Q Q' : Matrix (Fin n) (Fin n) L),
    (∀ x, σ (σ x) = x) → (∀ x, Valued.v (σ x) = Valued.v x) →
    (∀ i j, P i j ∈ Formalism.UG.intL L) → (∀ i j, Q' i j ∈ Formalism.UG.intL L) → Q * Q' = 1 →
    ∀ x : Matrix (Fin n') (Fin n) L,
    (∀ C : Matrix (Fin n') (Fin n') L, (∀ i j, σ (C i j) = - C j i) → (∀ i j, Valued.v (C i j) < 1) →
      (∀ i j, (C * x) i j ∈ Formalism.UG.intL L) →
      ψ ((δ * Matrix.trace (C * (x * A * Matrix.transpose ((x).map σ))) + σ (δ * Matrix.trace (C * (x * A * Matrix.transpose ((x).map σ))))) / 2) = 1) → (∀ C : Matrix (Fin n') (Fin n') L, (∀ i j, σ (C i j) = - C j i) → (∀ i j, Valued.v (C i j) < 1) →
      (∀ i j, (C * (P * x * Q)) i j ∈ Formalism.UG.intL L) →
      ψ ((δ * Matrix.trace (C * ((P * x * Q) * (Q' * A * Matrix.transpose (Q'.map σ)) * Matrix.transpose (((P * x * Q)).map σ))) + σ (δ * Matrix.trace (C * ((P * x * Q) * (Q' * A * Matrix.transpose (Q'.map σ)) * Matrix.transpose (((P * x * Q)).map σ))))) / 2) = 1) := by
  intro L _ _ σ δ n n' A ψ P Q Q' hσσ hσv hP hQ' hQQ' x hx C' hskew hv hint
  have hmap1 : (1 : Matrix (Fin n) (Fin n) L).map σ = 1 := Matrix.map_one σ (map_zero σ) (map_one σ)
  have hyQ' : (P * x * Q) * Q' = P * x := by rw [Matrix.mul_assoc, hQQ', Matrix.mul_one]
  have e1 : ∀ Z : Matrix (Fin n) (Fin n') L, Q * (Q' * Z) = Z := by
    intro Z; rw [← Matrix.mul_assoc, hQQ', Matrix.one_mul]
  have e2 : ∀ Z : Matrix (Fin n) (Fin n') L, (Q'.map σ)ᵀ * ((Q.map σ)ᵀ * Z) = Z := by
    intro Z
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, ← Matrix.map_mul, hQQ', hmap1, Matrix.transpose_one,
      Matrix.one_mul]
  have intMul : ∀ {a b c : ℕ} (M : Matrix (Fin a) (Fin b) L) (N : Matrix (Fin b) (Fin c) L),
      (∀ i j, M i j ∈ Formalism.UG.intL L) → (∀ i j, N i j ∈ Formalism.UG.intL L) → ∀ i j, (M * N) i j ∈ Formalism.UG.intL L := by
    intro a b c M N hM hN i j
    rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hM i k) (hN k j)
  have hPσ : ∀ i j, (P.map σ)ᵀ i j ∈ Formalism.UG.intL L := by
    intro i j
    show Valued.v (σ (P j i)) ≤ 1
    rw [hσv]; exact hP j i
  have htr : Matrix.trace ((P.map σ)ᵀ * C' * P * (x * A * (x.map σ)ᵀ)) =
      Matrix.trace (C' * ((P * x * Q) * (Q' * A * (Q'.map σ)ᵀ) * ((P * x * Q).map σ)ᵀ)) := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc, e1, e2]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hCx : (P.map σ)ᵀ * (C' * (P * x * Q)) * Q' = (P.map σ)ᵀ * C' * P * x := by
    calc (P.map σ)ᵀ * (C' * (P * x * Q)) * Q' = (P.map σ)ᵀ * (C' * ((P * x * Q) * Q')) := by
          simp only [Matrix.mul_assoc]
      _ = (P.map σ)ᵀ * (C' * (P * x)) := by rw [hyQ']
      _ = _ := by simp only [Matrix.mul_assoc]
  have := hx ((P.map σ)ᵀ * C' * P) ?_ ?_ ?_
  · rw [htr] at this; exact this
  · intro i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hσσ, hskew,
      Finset.sum_mul, ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  · intro i j
    have hlt : ∀ (a b : L), Valued.v a ≤ 1 → Valued.v b < 1 → Valued.v (a * b) < 1 := by
      intro a b ha hb
      rw [map_mul]
      calc Valued.v a * Valued.v b ≤ 1 * Valued.v b := mul_le_mul' ha le_rfl
        _ = Valued.v b := one_mul _
        _ < 1 := hb
    rw [Matrix.mul_apply]
    refine Valuation.map_sum_lt _ one_ne_zero fun k _ => ?_
    rw [mul_comm]
    refine hlt _ _ (hP k j) ?_
    rw [Matrix.mul_apply]
    refine Valuation.map_sum_lt _ one_ne_zero fun l _ => ?_
    exact hlt _ _ (hPσ i l) (hv l k)
  · intro i j
    rw [← hCx]
    exact intMul _ _ (intMul _ _ hPσ hint) hQ' i j

end GlobalTheory
