import Mathlib

noncomputable def UpperTheory.Reformulated.B.BlockFourMatrices.blk4 :
    {R : Type} →
      {n : ℕ} →
        Matrix (Fin n) (Fin n) R →
          Matrix (Fin n) (Fin n) R →
            Matrix (Fin n) (Fin n) R → Matrix (Fin n) (Fin n) R → Matrix (Fin (n + n)) (Fin (n + n)) R :=
    fun {R : Type} {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) R) ↦
      (Matrix.fromBlocks a b c d).submatrix (⇑finSumFinEquiv.symm : Fin (n + n) → Fin n ⊕ Fin n)
        (⇑finSumFinEquiv.symm : Fin (n + n) → Fin n ⊕ Fin n)

theorem UpperTheory.Reformulated.B.BlockFourMatrices.main :
    ∀ {R S : Type} {m : ℕ} (f : R → S) (a b c d : Matrix (Fin m) (Fin m) R),
      (UpperTheory.Reformulated.B.BlockFourMatrices.blk4 a b c d).map f = UpperTheory.Reformulated.B.BlockFourMatrices.blk4 (a.map f) (b.map f) (c.map f) (d.map f) := by
  intro R S m f a b c d
  unfold UpperTheory.Reformulated.B.BlockFourMatrices.blk4
  rw [← Matrix.submatrix_map, Matrix.fromBlocks_map]
