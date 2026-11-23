import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne

noncomputable section

open Matrix
open scoped Classical

namespace GlobalTheory.OrbDesc

section Blocks

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {a b : ℕ}

def side (e : ι ≃ Fin a ⊕ Fin b) (i : ι) : Bool := (e i).isRight

def uMat (e : ι ≃ Fin a ⊕ Fin b) (X : Fin a → Fin b → K) : Matrix ι ι K :=
  Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)

theorem uMat_add (e : ι ≃ Fin a ⊕ Fin b) (X Y : Fin a → Fin b → K) :
    uMat e (X + Y) = uMat e X * uMat e Y := by
  simp only [uMat, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  congr 1
  simp [Matrix.of_add_of, add_comm]

theorem uMat_zero (e : ι ≃ Fin a ⊕ Fin b) : uMat e (0 : Fin a → Fin b → K) = 1 := by
  simp [uMat]

def uGL (e : ι ≃ Fin a ⊕ Fin b) (X : Fin a → Fin b → K) : GL ι K :=
  ⟨uMat e X, uMat e (-X), by rw [← uMat_add, add_neg_cancel, uMat_zero],
    by rw [← uMat_add, neg_add_cancel, uMat_zero]⟩

def uHom (e : ι ≃ Fin a ⊕ Fin b) : Multiplicative (Fin a → Fin b → K) →* GL ι K where
  toFun X := uGL e X.toAdd
  map_one' := Units.ext (uMat_zero e)
  map_mul' X Y := Units.ext (uMat_add e X.toAdd Y.toAdd)

def blockPar (e : ι ≃ Fin a ⊕ Fin b) : Subgroup (GL ι K) where
  carrier := {g | (g : Matrix ι ι K).BlockTriangular (side e)}
  one_mem' := by simpa using Matrix.blockTriangular_one
  mul_mem' := by
    intro g h hg hh
    simpa using Matrix.BlockTriangular.mul hg hh
  inv_mem' := by
    intro g hg
    have : Invertible (g : Matrix ι ι K) := Units.invertible g
    simp only [Set.mem_setOf_eq, Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hg

def blockParOpp (e : ι ≃ Fin a ⊕ Fin b) : Subgroup (GL ι K) where
  carrier := {g | (g : Matrix ι ι K).BlockTriangular (fun i => OrderDual.toDual (side e i))}
  one_mem' := by simpa using Matrix.blockTriangular_one
  mul_mem' := by
    intro g h hg hh
    simpa using Matrix.BlockTriangular.mul hg hh
  inv_mem' := by
    intro g hg
    have : Invertible (g : Matrix ι ι K) := Units.invertible g
    simp only [Set.mem_setOf_eq, Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hg

def blockLevi (e : ι ≃ Fin a ⊕ Fin b) : Subgroup (GL ι K) := blockPar e ⊓ blockParOpp e

def blockUni (e : ι ≃ Fin a ⊕ Fin b) : Subgroup (GL ι K) := (uHom e).range

end Blocks

section Sums

variable {H : Type} [Group H]

def wt (T L U : Subgroup H) (Ψ : H → ℂ) (x : H) : ℂ :=
  (GlobalTheory.LKLoc.volRat U (GlobalTheory.LKLoc.locPart T L x) : ℂ) * Ψ x

def dsum (T L U : Subgroup H) (Ψ : H → ℂ) : ℂ :=
  ∑ᶠ q : DoubleCoset.Quotient (T : Set H) (L : Set H), wt T L U Ψ (Quotient.out q)

end Sums

end GlobalTheory.OrbDesc
