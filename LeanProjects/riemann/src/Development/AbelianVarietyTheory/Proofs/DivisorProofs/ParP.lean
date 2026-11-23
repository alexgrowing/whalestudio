import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LeviDesc

def cavg {G : Type} [Group G] (K : Subgroup G) (f : G → ℂ) (x : G) : ℂ :=
  avg fun k : K => f ((k : G)⁻¹ * x * k)

def adL {k : Type} [Field k] {a b : ℕ} (A : GL (Fin a) k) (B : Matrix (Fin b) (Fin b) k) :
    Matrix (Fin a) (Fin b) k →ₗ[k] Matrix (Fin a) (Fin b) k where
  toFun X := X - (A⁻¹ : GL (Fin a) k).val * X * B
  map_add' X Y := by simp only [Matrix.mul_add, Matrix.add_mul]; abel
  map_smul' c X := by simp [Matrix.mul_smul, Matrix.smul_mul, smul_sub]

variable {E : Type} [Field E] [NumberField E]

def parP (a n : ℕ) (w : Pl E) : Subgroup (GLw n w) where
  carrier := {g | (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)).BlockTriangular fun i : Fin n => decide (a ≤ (i : ℕ))}
  mul_mem' {g h} hg hh := by
    simp only [Set.mem_ofPred_eq, Units.val_mul] at *
    exact hg.mul hh
  one_mem' := by
    simp only [Set.mem_ofPred_eq, Units.val_one]
    exact Matrix.blockTriangular_one
  inv_mem' {g} hg := by
    let := g.invertible
    simp only [Set.mem_ofPred_eq, Matrix.coe_units_inv] at *
    exact Matrix.blockTriangular_inv_of_blockTriangular hg

def orbN {n a b : ℕ} (h : a + b = n) (w : Pl E) (f : GLw n w → ℂ) (m : GLw a w × GLw b w) : ℂ :=
  hint (intMat a b w) fun X => cavg (GlobalTheory.LFun.KGL w n) f
    ((blk h w 1 (Multiplicative.toAdd X))⁻¹ * blk h w m 0 * blk h w 1 (Multiplicative.toAdd X))

end GlobalTheory.LeviDesc
