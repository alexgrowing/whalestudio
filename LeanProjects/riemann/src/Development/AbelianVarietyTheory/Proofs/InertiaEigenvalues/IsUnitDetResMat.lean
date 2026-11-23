import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.ResR

variable {l : ℕ} [Fact l.Prime] {r : ℕ}

def frobMat (ω : Fin r → ↥(MaximalUnramifiedExtension l)) : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l) := Matrix.of fun m k => fr l m (ω k)

def resMat (n : Type) [Fintype n] [DecidableEq n] (ω : Fin r → ↥(MaximalUnramifiedExtension l)) :
    Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) :=
  Matrix.kroneckerMap (· * ·) (1 : Matrix n n ↥(MaximalUnramifiedExtension l)) (frobMat ω)

theorem resMat_apply (n : Type) [Fintype n] [DecidableEq n] (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (a b : n × Fin r) :
    resMat n ω a b = if a.1 = b.1 then fr l a.2 (ω b.2) else 0 := by
  simp [resMat, frobMat, Matrix.kroneckerMap_apply, Matrix.one_apply]

theorem isUnit_det_resMat (n : Type) [Fintype n] [DecidableEq n] (ω : Fin r → ↥(MaximalUnramifiedExtension l))
    (hdet : (frobMat ω).det ≠ 0) : IsUnit (resMat n ω).det := by
  rw [resMat, Matrix.det_kronecker, Matrix.det_one, one_pow, one_mul]
  exact (isUnit_iff_ne_zero.2 hdet).pow _

def resGL (n : Type) [Fintype n] [DecidableEq n] (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (hdet : (frobMat ω).det ≠ 0) :
    GL (n × Fin r) ↥(MaximalUnramifiedExtension l) :=
  Matrix.GeneralLinearGroup.mk'' (resMat n ω) (isUnit_det_resMat n ω hdet)

def blockGL {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (U : Fin r → GL n R) :
    GL (n × Fin r) R where
  val := Matrix.blockDiagonal fun m => (U m : Matrix n n R)
  inv := Matrix.blockDiagonal fun m => (((U m)⁻¹ : GL n R) : Matrix n n R)
  val_inv := by rw [← Matrix.blockDiagonal_mul]; simp only [Units.mul_inv]; exact Matrix.blockDiagonal_one
  inv_val := by rw [← Matrix.blockDiagonal_mul]; simp only [Units.inv_mul]; exact Matrix.blockDiagonal_one

variable (P : LocPrime l) {n : Type} [Fintype n] [DecidableEq n]

def U0 (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (hdet : (frobMat ω).det ≠ 0) (U : Fin r → GL n P.R.BdR) : GL (n × Fin r) P.R.BdR :=
  (Units.map ((kd P).mapMatrix : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) →+* Matrix (n × Fin r) (n × Fin r) P.R.BdR).toMonoidHom
    (resGL n ω hdet))⁻¹ * blockGL U

def Ymat (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (A₀ : GL (n × Fin r) P.R.B) : Matrix (n × Fin r) (n × Fin r) P.R.B :=
  (resMat n ω).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) * (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B)

def colv (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (A₀ : GL (n × Fin r) P.R.B) (c : n × Fin r) (i : n) : P.R.B :=
  ∑ k, algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (ω k) * (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) (i, k) c

def LatC (U : Fin r → GL n P.R.BdR) (x y : Fin r × n) (a : n → P.R.B) : Prop :=
  (∀ i, P.φB^[r] (a i) = a i) ∧ ∀ m : Fin r, ∃ w : n → P.R.BdR, (∀ i, w i ∈ Fil P 0) ∧
    (fun i => ev P m (a i)) = ((U m : Matrix n n P.R.BdR) * Matrix.diagonal fun j => tz P (eps x y (m, j))).mulVec w

end GlobalTheory.PMon.ResR

end
