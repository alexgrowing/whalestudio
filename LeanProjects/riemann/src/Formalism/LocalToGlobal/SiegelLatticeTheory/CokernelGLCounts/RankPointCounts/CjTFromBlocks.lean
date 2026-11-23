import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LiftOrbOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfL

noncomputable section

open Matrix
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents

section Block

variable {K : Type*} [CommRing K] (cj : K →+* K) {n : Type*} [Fintype n] [DecidableEq n]

def cjT {m n : Type*} (A : Matrix m n K) : Matrix n m K := (A.map cj)ᵀ

theorem cjT_mul {l m n : Type*} [Fintype m] (A : Matrix l m K) (B : Matrix m n K) :
    cjT cj (A * B) = cjT cj B * cjT cj A := by
  unfold cjT
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem cjT_cjT {m n : Type*} (h : ∀ x, cj (cj x) = x) (A : Matrix m n K) : cjT cj (cjT cj A) = A := by
  ext i j; simp [cjT, h]

theorem cjT_fromBlocks {a b c d : Type*} (A : Matrix a c K) (B : Matrix a d K) (C : Matrix b c K) (D : Matrix b d K) :
    cjT cj (Matrix.fromBlocks A B C D) = Matrix.fromBlocks (cjT cj A) (cjT cj C) (cjT cj B) (cjT cj D) := by
  unfold cjT
  rw [Matrix.fromBlocks_map, Matrix.fromBlocks_transpose]

theorem cjT_zero {m n : Type*} : cjT cj (0 : Matrix m n K) = 0 := by
  ext i j; simp [cjT]

theorem block_cong (h : ∀ x, cj (cj x) = x) (G₁ G₁' X X' G₂ G₂' Mm U : Matrix n n K)
    (h1 : cjT cj Mm * G₁ * Mm = G₁') (h2 : cjT cj Mm * X * U = X') (h3 : cjT cj U * G₂ * U = G₂') :
    cjT cj (Matrix.fromBlocks Mm 0 0 U) * Matrix.fromBlocks G₁ X (cjT cj X) G₂ * Matrix.fromBlocks Mm 0 0 U =
      Matrix.fromBlocks G₁' X' (cjT cj X') G₂' := by
  rw [cjT_fromBlocks, cjT_zero, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  rw [h1, h3, ← h2]
  congr 1 <;> first
    | (simp only [Matrix.mul_assoc]; done)
    | (rw [cjT_mul, cjT_mul, cjT_cjT cj h]; simp only [Matrix.mul_assoc])

end Block

section GaBlocks

variable {D : D7} (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)

def gDiag (p : PlF D) (T : D.host.E) : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep :=
  Matrix.of fun a b => frFac δ p b * (M p).L.cj (frFac δ p a) *
    (D.s.atP p).ιE (if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then -T else 0)

theorem gaLoc_blocks (hA : ∀ q, Agree δ M q) (p : PlF D) (T T' : D.host.E) (Z : MatZ D) :
    GaLoc M δ p T T' Z = Matrix.fromBlocks (gDiag δ M p T) (ZhatLoc M δ p Z)
      (cjT ((M p).L.cj : (D.s.atP p).Ep →+* (D.s.atP p).Ep) (ZhatLoc M δ p Z)) (gDiag δ M p T') := by
  have hcj : (M p).L.cj = (D.s.atP p).cj := (hA p).2.2.1
  ext a b
  rcases a with a | a <;> rcases b with b | b
  · simp [GaLoc, gDiag, Ga, phi]
  · simp [GaLoc, ZhatLoc, Ga, phi]
  · simp only [GaLoc, Matrix.of_apply, phi, Sum.elim_inl, Sum.elim_inr, Ga, Matrix.fromBlocks_apply₂₁,
      Matrix.conjTranspose_apply, cjT, Matrix.transpose_apply, Matrix.map_apply, ZhatLoc, RingHom.coe_coe]
    rw [map_mul, map_mul, (M p).L.cj_cj, hcj, Formalism.MainNotions.S.Inh.tie_cj_iota]
    ring
  · simp [GaLoc, gDiag, Ga, phi]

end GaBlocks

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents
