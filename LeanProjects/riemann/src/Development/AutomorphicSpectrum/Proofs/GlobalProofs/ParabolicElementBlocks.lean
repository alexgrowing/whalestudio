import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QLB

section Alg

variable {F : Type} [Field F]

theorem pEl_coe {r c : ℕ} (m₁ : GL (Fin r) F) (B : Matrix (Fin r) (Fin c) F) (m₂ : GL (Fin c) F) :
    (pEl m₁ B m₂ : Matrix (Fin (r + c)) (Fin (r + c)) F) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (m₁ : Matrix (Fin r) (Fin r) F) B 0 (m₂ : Matrix (Fin c) (Fin c) F)) := rfl

section Blocks

variable {r d c : ℕ} (A : Matrix (Fin r) (Fin r) F) (B : Matrix (Fin r) (Fin c) F)
  (C : Matrix (Fin d) (Fin r) F) (D : Matrix (Fin d) (Fin c) F)

theorem bAA_reindex : bAA (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A B C D)) = A := by
  ext i j; simp [bAA]

theorem bAD_reindex : bAD (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A B C D)) = B := by
  ext i j; simp [bAD]

theorem bDA_reindex : bDA (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A B C D)) = C := by
  ext i j; simp [bDA]

theorem bDD_reindex : bDD (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A B C D)) = D := by
  ext i j; simp [bDD]

end Blocks

theorem pEl_det {r c : ℕ} (m₁ : GL (Fin r) F) (B : Matrix (Fin r) (Fin c) F) (m₂ : GL (Fin c) F) :
    (pEl m₁ B m₂ : Matrix (Fin (r + c)) (Fin (r + c)) F).det =
      (m₁ : Matrix (Fin r) (Fin r) F).det * (m₂ : Matrix (Fin c) (Fin c) F).det := by
  rw [pEl_coe, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

end Alg

end GlobalTheory.CompanionTheory.QLB
