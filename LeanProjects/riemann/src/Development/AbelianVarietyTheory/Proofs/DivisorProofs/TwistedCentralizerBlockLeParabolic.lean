import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTerBis

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LeviDesc

theorem intertwiner_eq_zero_of_isCoprime {K : Type} [Field K] {a b : ℕ}
    (A : Matrix (Fin a) (Fin a) K) (B : Matrix (Fin b) (Fin b) K) (C : Matrix (Fin b) (Fin a) K)
    (hc : IsCoprime A.charpoly B.charpoly) (hC : C * A = B * C) : C = 0 := by
  first
  | exact @_root_.GlobalTheory.IntertwiningOperators.main
  | exact _root_.GlobalTheory.IntertwiningOperators.main
  | (apply _root_.GlobalTheory.IntertwiningOperators.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntertwiningOperators.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntertwiningOperators.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntertwiningOperators.main ..)

theorem twCent_blk_le_parP : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E)
    (m : GLw a w × GLw b w), (m.1.val.charpoly * m.2.val.charpoly).Separable →
    twCent (MonoidHom.id (GLw n w)) (blk h w m 0) ≤ GlobalTheory.LeviDesc.parP a n w := by
  intro E _ _ n a b h w m hsep g hg
  have hcop := hsep.isCoprime
  have hM : IsUnit (Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks m.1.val (m.1.val * (0 : Matrix (Fin a) (Fin b) (w.adicCompletion E))) 0 m.2.val)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_reindex_self, Matrix.mul_zero, Matrix.det_fromBlocks_zero₁₂]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp m.1.isUnit).mul ((Matrix.isUnit_iff_isUnit_det _).mp m.2.isUnit)
  have hval : ((blk h w m 0 : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
      Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (Matrix.fromBlocks m.1.val (m.1.val * (0 : Matrix (Fin a) (Fin b) (w.adicCompletion E))) 0 m.2.val) := by
    simp only [blk]
    rw [dif_pos hM]
    rfl
  rw [Matrix.mul_zero] at hval
  have hc : (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * (blk h w m 0 : GLw n w) =
      ((blk h w m 0 : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * g := by
    have := congrArg Units.val (show g * blk h w m 0 = blk h w m 0 * MonoidHom.id _ g from hg)
    simpa using this
  rw [hval] at hc
  set e := finSumFinEquiv.trans (finCongr h) with he
  set g' := Matrix.reindex e.symm e.symm (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hg'
  have hgg : (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Matrix.reindex e e g' := by
    simp [hg']
  rw [hgg, ← Matrix.fromBlocks_toBlocks g'] at hc
  have hc2 := congrArg (Matrix.reindex e.symm e.symm) hc
  simp only [Matrix.reindex_apply, Equiv.symm_symm, Matrix.submatrix_mul_equiv, Matrix.submatrix_submatrix,
    Equiv.symm_comp_self, Matrix.submatrix_id_id, Matrix.fromBlocks_multiply] at hc2
  rw [Matrix.fromBlocks_inj] at hc2
  have hC : g'.toBlocks₂₁ * m.1.val = m.2.val * g'.toBlocks₂₁ := by
    have := hc2.2.2.1
    simpa using this
  have hC0 := intertwiner_eq_zero_of_isCoprime _ _ _ hcop hC
  show (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)).BlockTriangular fun i : Fin n => decide (a ≤ (i : ℕ))
  intro i j hij
  have hi : a ≤ (i : ℕ) := by
    by_contra hc'
    revert hij
    simp only [hc', decide_false]
    cases decide (a ≤ (j : ℕ)) <;> decide
  have hj : ¬ a ≤ (j : ℕ) := by
    intro hc'
    revert hij
    simp only [hc', decide_true]
    cases decide (a ≤ (i : ℕ)) <;> decide
  have hie : i = e (Sum.inr ⟨(i : ℕ) - a, by omega⟩) := by
    ext; simp [he]; omega
  have hje : j = e (Sum.inl ⟨(j : ℕ), by omega⟩) := by
    ext; simp [he]
  rw [hgg, hie, hje]
  have : g'.toBlocks₂₁ ⟨(i : ℕ) - a, by omega⟩ ⟨(j : ℕ), by omega⟩ = 0 := by rw [hC0]; rfl
  simpa [Matrix.toBlocks₂₁] using this

end GlobalTheory.LeviDesc
