import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
  Formalism.L2.Host GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.BCT.CtLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev blkEq {a b n : ℕ} (h : a + b = n) : Fin a ⊕ Fin b ≃ Fin n := finSumFinEquiv.trans (finCongr h)

def dgMat {R : Type} [CommRing R] {a b n : ℕ} (h : a + b = n) (A : Matrix (Fin a) (Fin a) R)
    (D : Matrix (Fin b) (Fin b) R) : Matrix (Fin n) (Fin n) R :=
  reindex (blkEq h) (blkEq h) (fromBlocks A 0 0 D)

theorem dgMat_mul {R : Type} [CommRing R] {a b n : ℕ} (h : a + b = n) (A A' : Matrix (Fin a) (Fin a) R)
    (D D' : Matrix (Fin b) (Fin b) R) : dgMat h A D * dgMat h A' D' = dgMat h (A * A') (D * D') := by
  simp only [dgMat, reindex_apply, submatrix_mul_equiv, fromBlocks_multiply]
  simp

theorem dgMat_one {R : Type} [CommRing R] {a b n : ℕ} (h : a + b = n) :
    dgMat h (1 : Matrix (Fin a) (Fin a) R) (1 : Matrix (Fin b) (Fin b) R) = 1 := by
  rw [dgMat, fromBlocks_one, reindex_apply, submatrix_one_equiv]

def dgM {a b n : ℕ} (h : a + b = n) (w : Pl E) : GLw a w × GLw b w →* GLw n w where
  toFun k := ⟨dgMat h k.1.val k.2.val, dgMat h (k.1⁻¹).val (k.2⁻¹).val,
    by rw [dgMat_mul, Units.mul_inv, Units.mul_inv, dgMat_one],
    by rw [dgMat_mul, Units.inv_mul, Units.inv_mul, dgMat_one]⟩
  map_one' := Units.ext (by simp [dgMat_one])
  map_mul' x y := Units.ext (by simp [dgMat_mul])

theorem dgM_val {a b n : ℕ} (h : a + b = n) (w : Pl E) (k : GLw a w × GLw b w) :
    (dgM h w k).val = dgMat h k.1.val k.2.val := rfl

def lev₁ {a b n : ℕ} (h : a + b = n) (w : Pl E) (N : Subgroup (GLw n w)) (μ : (w.adicCompletion E)ˣ →* ℂˣ) :
    Subgroup (GLw a w) :=
  GlobalTheory.LFun.KGL w a ⊓ N.comap ((dgM h w).comp (MonoidHom.inl _ _)) ⊓ μ.ker.comap GeneralLinearGroup.det

def lev₂ {a b n : ℕ} (h : a + b = n) (w : Pl E) (N : Subgroup (GLw n w)) (μ : (w.adicCompletion E)ˣ →* ℂˣ) :
    Subgroup (GLw b w) :=
  GlobalTheory.LFun.KGL w b ⊓ N.comap ((dgM h w).comp (MonoidHom.inr _ _)) ⊓ μ.ker.comap GeneralLinearGroup.det

theorem blk_val {n a b : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    (blk h w m X).val = reindex (blkEq h) (blkEq h) (fromBlocks m.1.val (m.1.val * X) 0 m.2.val) := by
  have hu : IsUnit (reindex (blkEq h) (blkEq h) (fromBlocks m.1.val (m.1.val * X) 0 m.2.val)) := by
    rw [isUnit_iff_isUnit_det, det_reindex_self, det_fromBlocks_zero₂₁]
    exact (m.1.isUnit.map detMonoidHom).mul (m.2.isUnit.map detMonoidHom)
  unfold blk
  simp only
  rw [dif_pos hu]
  rfl

end GlobalTheory.BCT.CtLevel
