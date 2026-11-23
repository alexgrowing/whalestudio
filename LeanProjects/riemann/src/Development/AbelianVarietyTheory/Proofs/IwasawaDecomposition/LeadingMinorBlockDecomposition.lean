import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockOrderedSumEquivTrueIndex
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.FlagFibre

theorem lminor_block : ∀ (r p q : ℕ) (e : Fin r ≃ Fin p ⊕ Fin q), IsBlockSL2Embedding e → ∀ H : Matrix (Fin r) (Fin r) ℂ, IsUnit (reindex e e H).toBlocks₂₂.det → (∀ (i : Fin (r + 1)) (k : Fin (q + 1)), (i : ℕ) = k → lminor H i = lminor (reindex e e H).toBlocks₂₂ k) ∧ ∀ (i : Fin (r + 1)) (k : Fin (p + 1)), (i : ℕ) = q + k → lminor H i = (reindex e e H).toBlocks₂₂.det * lminor (schur (reindex e e H)) k := by
  intro r p q e he H hH
  constructor
  · rintro ⟨i, hi⟩ ⟨k, hk⟩ h
    obtain rfl : i = k := h
    unfold lminor
    congr 1
    ext a b
    simp only [submatrix_apply, toBlocks₂₂, reindex_apply, of_apply]
    congr 1 <;> exact Fin.ext (by rw [he.2]; rfl)
  · rintro ⟨i, hi⟩ ⟨k, hk⟩ h
    obtain rfl : i = q + k := h
    obtain ⟨f0, hf0⟩ := exists_isBlockOrderedSumEquiv k q
    let f : Fin (q + k) ≃ Fin k ⊕ Fin q := (finCongr (add_comm q k)).trans f0
    have hf : IsBlockSL2Embedding f := ⟨fun a => hf0.1 a, fun a => hf0.2 a⟩
    let c : Fin k → Fin p := Fin.castLE (Nat.le_of_lt_succ hk)
    let G : Matrix (Fin k ⊕ Fin q) (Fin k ⊕ Fin q) ℂ := (reindex e e H).submatrix (Sum.map c id) (Sum.map c id)
    have key : ∀ a, Fin.castLE (Nat.le_of_lt_succ hi) (f.symm a) = e.symm (Sum.map c id a) := by
      rintro (a | a) <;> apply Fin.ext
      · simp only [Fin.val_castLE, Sum.map_inl, hf.1, he.1, c]
      · simp only [Fin.val_castLE, Sum.map_inr, hf.2, he.2, id]
    have h1 : lminor H ⟨q + k, hi⟩ = G.det := by
      unfold lminor
      rw [← det_submatrix_equiv_self f.symm]
      congr 1
      ext a b
      simp only [G, submatrix_apply, reindex_apply, ← key]
    have h2 : G.toBlocks₂₂ = (reindex e e H).toBlocks₂₂ := rfl
    rw [h1, det_eq_mul_schur (h2 ▸ hH), h2]
    rfl

end GlobalTheory.FlagFibre
