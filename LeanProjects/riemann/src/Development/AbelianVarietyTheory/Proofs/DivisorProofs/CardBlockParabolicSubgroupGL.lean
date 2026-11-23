import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowBlockIndicatorFromLtIff
open NumberField UniqueFactorizationMonoid GlobalTheory.StdLoc

noncomputable section

namespace GlobalTheory.StdLoc

def blockMat {R : Type} [CommRing R] {a b : ℕ} (A : Matrix (Fin a) (Fin a) R) (B : Matrix (Fin a) (Fin b) R)
    (D : Matrix (Fin b) (Fin b) R) : Matrix (Fin (a + b)) (Fin (a + b)) R :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A B 0 D)

theorem det_blockMat {R : Type} [CommRing R] {a b : ℕ} (A : Matrix (Fin a) (Fin a) R) (B : Matrix (Fin a) (Fin b) R)
    (D : Matrix (Fin b) (Fin b) R) : (blockMat A B D).det = A.det * D.det := by
  rw [blockMat, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

def blockParMk {R : Type} [CommRing R] {a b : ℕ}
    (x : GL (Fin a) R × GL (Fin b) R × Matrix (Fin a) (Fin b) R) : blockPar R a (a + b) :=
  ⟨Matrix.GeneralLinearGroup.mk'' (blockMat x.1.1 x.2.2 x.2.1.1) (by
      rw [det_blockMat]
      exact ((Matrix.isUnit_iff_isUnit_det _).1 x.1.isUnit).mul ((Matrix.isUnit_iff_isUnit_det _).1 x.2.1.isUnit)), by
    rw [mem_blockPar]
    intro i j hj hi
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    show blockMat x.1.1 x.2.2 x.2.1.1 _ _ = 0
    rcases i with i | i
    · exact absurd hi (by simp)
    rcases j with j | j
    · simp only [blockMat, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
        Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
    · exact absurd hj (by simp)⟩

theorem blockParMk_val {R : Type} [CommRing R] {a b : ℕ}
    (x : GL (Fin a) R × GL (Fin b) R × Matrix (Fin a) (Fin b) R) :
    ((blockParMk x).1 : Matrix (Fin (a + b)) (Fin (a + b)) R) = blockMat x.1.1 x.2.2 x.2.1.1 := rfl

theorem blockParMk_bijective {R : Type} [CommRing R] {a b : ℕ} :
    Function.Bijective (blockParMk (R := R) (a := a) (b := b)) := by
  constructor
  · rintro ⟨A, D, B⟩ ⟨A', D', B'⟩ h
    have h1 : blockMat A.1 B D.1 = blockMat A'.1 B' D'.1 := by
      have := congrArg (fun g : blockPar R a (a + b) => (g.1 : Matrix (Fin (a + b)) (Fin (a + b)) R)) h
      simpa only [blockParMk_val] using this
    have h2 := (Matrix.reindex finSumFinEquiv finSumFinEquiv).injective h1
    obtain ⟨hA, hB, -, hD⟩ := Matrix.fromBlocks_inj.1 h2
    exact Prod.ext (Units.ext hA) (Prod.ext (Units.ext hD) hB)
  · rintro ⟨g, hg⟩
    set M : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) R :=
      (Matrix.reindex finSumFinEquiv finSumFinEquiv).symm (g : Matrix (Fin (a + b)) (Fin (a + b)) R) with hM
    have h0 : M.toBlocks₂₁ = 0 := by
      ext i j
      exact (mem_blockPar g).1 hg (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) (by simp) (by simp)
    have hb : blockMat M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₂ = g := by
      rw [blockMat, ← h0, Matrix.fromBlocks_toBlocks, hM, Equiv.apply_symm_apply]
    have hu : IsUnit (M.toBlocks₁₁.det * M.toBlocks₂₂.det) := by
      rw [← det_blockMat _ M.toBlocks₁₂, hb]
      exact (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
    refine ⟨(Matrix.GeneralLinearGroup.mk'' _ (isUnit_of_mul_isUnit_left hu),
      Matrix.GeneralLinearGroup.mk'' _ (isUnit_of_mul_isUnit_right hu), M.toBlocks₁₂), ?_⟩
    exact Subtype.ext (Units.ext hb)

theorem card_blockPar (R : Type) [CommRing R] [Finite R] (a d : ℕ) (h : a ≤ d) :
    Nat.card (blockPar R a d) =
      Nat.card (GL (Fin a) R) * Nat.card (GL (Fin (d - a)) R) * Nat.card R ^ (a * (d - a)) := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left, ← Nat.card_eq_of_bijective _ blockParMk_bijective, Nat.card_prod, Nat.card_prod,
    mul_assoc]
  congr 2
  show Nat.card (Fin a → Fin b → R) = _
  rw [Nat.card_fun, Nat.card_fun, ← pow_mul]
  simp [mul_comm]

end GlobalTheory.StdLoc
