import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta MeasureTheory
open scoped Matrix Kronecker

noncomputable section

namespace GlobalTheory

namespace FockEmb

theorem Jpq_eq_diagonal (p q : ℕ) :
    Formalism.UG.Jpq p q = Matrix.diagonal (fun a => if a.isLeft then (1 : ℂ) else -1) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem reindex_kron_J (p q r s : ℕ) :
    Matrix.reindex (lineEquiv p q r s) (lineEquiv p q r s)
      (Formalism.UG.Jpq p q ⊗ₖ Formalism.UG.Jpq r s) = Formalism.UG.Jpq (p * r + q * s) (p * s + q * r) := by
  rw [Jpq_eq_diagonal, Jpq_eq_diagonal, Jpq_eq_diagonal, Matrix.diagonal_kronecker_diagonal,
    Matrix.reindex_apply, Matrix.submatrix_diagonal_equiv]
  congr 1
  funext x
  obtain ⟨l, rfl⟩ := (lineEquiv p q r s).surjective x
  simp only [Function.comp, Equiv.symm_apply_apply, lineEquiv_isLeft]
  rcases l with ⟨a | a, c | c⟩ <;> simp [linePos]

def kronGL (p q r s : ℕ) :
    GL (Ix p q) ℂ × GL (Ix r s) ℂ →* GL (Ix (p * r + q * s) (p * s + q * r)) ℂ where
  toFun x := Units.map (Matrix.reindexAlgEquiv ℂ ℂ (lineEquiv p q r s)).toMonoidHom
    (Matrix.GeneralLinearGroup.kronecker x.1 x.2)
  map_one' := by
    apply Units.ext
    simp [Matrix.GeneralLinearGroup.kronecker]
  map_mul' x y := by
    rw [← map_mul]
    congr 1
    apply Units.ext
    simp [Matrix.GeneralLinearGroup.kronecker, Matrix.mul_kronecker_mul]

theorem kronGL_val {p q r s : ℕ} (g : GL (Ix p q) ℂ) (h : GL (Ix r s) ℂ) :
    ((kronGL p q r s (g, h) : GL _ ℂ) : Mat (p * r + q * s) (p * s + q * r)) =
      Matrix.reindex (lineEquiv p q r s) (lineEquiv p q r s)
        ((g : Mat p q) ⊗ₖ (h : Mat r s)) := rfl

theorem mem_Upq_iff {p q : ℕ} (g : GL (Ix p q) ℂ) :
    g ∈ Formalism.UG.Upq p q ↔ (g : Mat p q)ᴴ * Formalism.UG.Jpq p q * (g : Mat p q) = Formalism.UG.Jpq p q :=
  Iff.rfl

theorem kronGL_mem {p q r s : ℕ} {g : GL (Ix p q) ℂ} {h : GL (Ix r s) ℂ}
    (hg : g ∈ Formalism.UG.Upq p q) (hh : h ∈ Formalism.UG.Upq r s) :
    kronGL p q r s (g, h) ∈ Formalism.UG.Upq (p * r + q * s) (p * s + q * r) := by
  rw [mem_Upq_iff] at *
  rw [kronGL_val, ← reindex_kron_J]
  simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    hg, hh]

theorem kronGL_det {p q r s : ℕ} (g : GL (Ix p q) ℂ) (h : GL (Ix r s) ℂ) :
    ((kronGL p q r s (g, h) : GL _ ℂ) : Mat (p * r + q * s) (p * s + q * r)).det =
      (g : Mat p q).det ^ (r + s) * (h : Mat r s).det ^ (p + q) := by
  rw [kronGL_val, Matrix.det_reindex_self, Matrix.det_kronecker]
  simp

end FockEmb

open FockEmb in

theorem exists_cover_tensor_hom :
    ∀ (p q r s : ℕ) (T0 : GrpData (p * r + q * s) (p * s + q * r)) (T1 : GrpData p q) (T2 : GrpData r s), ∃ emb : T1.G × T2.G →* T0.G, (∀ g h, ((T0.cov (emb (g, h)) : GL _ ℂ) : Mat (p * r + q * s) (p * s + q * r)) = Matrix.reindex (lineEquiv p q r s) (lineEquiv p q r s) (Matrix.kroneckerMap (· * ·) ((T1.cov g : GL _ ℂ) : Mat p q) ((T2.cov h : GL _ ℂ) : Mat r s))) ∧ ∀ g h, T0.sq (emb (g, h)) = T1.sq g ^ (r + s) * T2.sq h ^ (p + q) := by
  intro p q r s T0 T1 T2
  have key : ∀ x : T1.G × T2.G, ∃! y : T0.G, T0.cov y = kronGL p q r s (T1.cov x.1, T2.cov x.2) ∧
      T0.sq y = T1.sq x.1 ^ (r + s) * T2.sq x.2 ^ (p + q) := by
    intro x
    apply T0.bij _ (kronGL_mem (T1.cov_mem _) (T2.cov_mem _))
    rw [kronGL_det, ← T1.sq_sq, ← T2.sq_sq]
    push_cast
    ring
  choose f hf huniq using key
  refine ⟨MonoidHom.mk' f ?_, fun g h => ?_, fun g h => (hf (g, h)).2⟩
  · intro x y
    symm
    apply huniq
    constructor
    · rw [map_mul, (hf x).1, (hf y).1, ← map_mul]
      simp
    · rw [map_mul, (hf x).2, (hf y).2]
      simp only [Prod.fst_mul, Prod.snd_mul, map_mul, mul_pow]
      exact mul_mul_mul_comm _ _ _ _
  · show ((T0.cov (f (g, h)) : GL _ ℂ) : Mat (p * r + q * s) (p * s + q * r)) = _
    rw [(hf (g, h)).1]
    rfl

end GlobalTheory
