import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG

noncomputable section

namespace GlobalTheory

namespace WeylCell

section DiagConj

variable {L : Type} [Field L] {n : ℕ}

theorem gl_eq_diagonal_of_offdiag {D : GL (Fin n) L}
    (hD : ∀ i j, i ≠ j → (D : Matrix (Fin n) (Fin n) L) i j = 0) :
    (D : Matrix (Fin n) (Fin n) L) = Matrix.diagonal fun i => (D : Matrix (Fin n) (Fin n) L) i i := by
  ext i j
  by_cases h : i = j
  · subst h; simp
  · rw [Matrix.diagonal_apply_ne _ h, hD i j h]

theorem gl_diag_ne_zero_of_offdiag {D : GL (Fin n) L}
    (hD : ∀ i j, i ≠ j → (D : Matrix (Fin n) (Fin n) L) i j = 0) (i : Fin n) :
    (D : Matrix (Fin n) (Fin n) L) i i ≠ 0 := by
  intro h0
  have h := congrFun (congrFun (Units.mul_inv D) i) i
  rw [gl_eq_diagonal_of_offdiag hD, Matrix.diagonal_mul, h0, zero_mul, Matrix.one_apply_eq] at h
  exact zero_ne_one h

theorem gl_inv_eq_diagonal_of_offdiag {D : GL (Fin n) L}
    (hD : ∀ i j, i ≠ j → (D : Matrix (Fin n) (Fin n) L) i j = 0) :
    ((D⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      Matrix.diagonal fun i => ((D : Matrix (Fin n) (Fin n) L) i i)⁻¹ := by
  have hne := gl_diag_ne_zero_of_offdiag hD
  rw [Matrix.coe_units_inv]
  apply Matrix.inv_eq_left_inv
  calc Matrix.diagonal (fun i => ((D : Matrix (Fin n) (Fin n) L) i i)⁻¹) * (D : Matrix (Fin n) (Fin n) L)
      = Matrix.diagonal (fun i => ((D : Matrix (Fin n) (Fin n) L) i i)⁻¹) *
          Matrix.diagonal (fun i => (D : Matrix (Fin n) (Fin n) L) i i) :=
        congrArg _ (gl_eq_diagonal_of_offdiag hD)
    _ = 1 := by
        rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        congr 1
        funext i
        exact inv_mul_cancel₀ (hne i)

theorem gl_conj_apply_of_offdiag {D : GL (Fin n) L}
    (hD : ∀ i j, i ≠ j → (D : Matrix (Fin n) (Fin n) L) i j = 0) (g : GL (Fin n) L) (i j : Fin n) :
    ((D⁻¹ * g * D : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j =
      ((D : Matrix (Fin n) (Fin n) L) i i)⁻¹ * (g : Matrix (Fin n) (Fin n) L) i j *
        (D : Matrix (Fin n) (Fin n) L) j j := by
  rw [Units.val_mul, Units.val_mul, gl_inv_eq_diagonal_of_offdiag hD]
  conv_lhs => rw [gl_eq_diagonal_of_offdiag hD]
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.diagonal_apply_eq]

theorem conj_mem_unipB_of_offdiag {D : GL (Fin n) L}
    (hD : ∀ i j, i ≠ j → (D : Matrix (Fin n) (Fin n) L) i j = 0) {g : GL (Fin n) L}
    (hg : g ∈ unipB L (Fin n)) : D⁻¹ * g * D ∈ unipB L (Fin n) := by
  rw [mem_unipB] at hg ⊢
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [gl_conj_apply_of_offdiag hD, hg.1 i j hij, mul_zero, zero_mul]
  · rw [gl_conj_apply_of_offdiag hD, hg.2 i, mul_one, inv_mul_cancel₀ (gl_diag_ne_zero_of_offdiag hD i)]

theorem conj_mem_unipBLower_of_offdiag {D : GL (Fin n) L}
    (hD : ∀ i j, i ≠ j → (D : Matrix (Fin n) (Fin n) L) i j = 0) {g : GL (Fin n) L}
    (hg : g ∈ unipBLower L (Fin n)) : D⁻¹ * g * D ∈ unipBLower L (Fin n) := by
  rw [mem_unipBLower] at hg ⊢
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [gl_conj_apply_of_offdiag hD, hg.1 i j hij, mul_zero, zero_mul]
  · rw [gl_conj_apply_of_offdiag hD, hg.2 i, mul_one, inv_mul_cancel₀ (gl_diag_ne_zero_of_offdiag hD i)]

theorem weylRep_conj_offdiag {w : Equiv.Perm (Fin n)} {y t : GL (Fin n) L} (hy : IsWeylRep w y)
    (ht : ∀ i j, i ≠ j → (t : Matrix (Fin n) (Fin n) L) i j = 0) :
    ∀ i j, i ≠ j → ((y⁻¹ * t * y : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0 := by
  intro i j hij
  have hyi := hy.inv
  rw [Units.val_mul, Units.val_mul, gl_eq_diagonal_of_offdiag ht, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : l = w j
  · subst hl
    rw [Matrix.mul_diagonal, hyi i (w j) (by simpa using hij), zero_mul, zero_mul]
  · rw [hy l j hl, mul_zero]

end DiagConj

end WeylCell

end GlobalTheory

end

theorem GlobalTheory.WeylCell.diagConjU : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ)
    (y : GU σ n) (w : Equiv.Perm (Fin n)), IsWeylRep w (y : GL (Fin n) L) → ∀ (t : GU σ n),
    (∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) →
    IsBorelU (y⁻¹ * t * y) ∧ ∀ u ∈ cellU y, t⁻¹ * u * t ∈ cellU y := by
  intro L _ _ σ n y w hy t ht
  have hD := weylRep_conj_offdiag hy ht
  refine ⟨fun i j hij => ?_, fun u hu => ?_⟩
  · exact hD i j (ne_of_gt hij)
  · rw [cellU, Subgroup.mem_subgroupOf, mem_cell] at hu ⊢
    have e1 : (((t⁻¹ * u * t : GU σ n)) : GL (Fin n) L) =
        ((t : GL (Fin n) L))⁻¹ * (u : GL (Fin n) L) * (t : GL (Fin n) L) := rfl
    rw [e1]
    refine ⟨conj_mem_unipB_of_offdiag ht hu.1, ?_⟩
    have e2 : ((y : GL (Fin n) L))⁻¹ * (((t : GL (Fin n) L))⁻¹ * (u : GL (Fin n) L) * (t : GL (Fin n) L)) *
        (y : GL (Fin n) L) =
        ((y : GL (Fin n) L)⁻¹ * t * y)⁻¹ * ((y : GL (Fin n) L)⁻¹ * u * y) * ((y : GL (Fin n) L)⁻¹ * t * y) := by
      group
    rw [e2]
    exact conj_mem_unipBLower_of_offdiag hD hu.2
