import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

section General

variable {E : Type} [Field E] [StarRing E] {n : ℕ}

theorem gram_fromCols_smul (G : Matrix (Fin (n + n)) (Fin (n + n)) E) (e e' : Matrix (Fin (n + n)) (Fin n) E) (μ : E)
    (hμ : star μ = -μ) (h₁ : eᴴ * G * e = 0) (h₂ : e'ᴴ * G * e' = 0) (h₃ : e'ᴴ * G * e = 1) (h₄ : eᴴ * G * e' = 1) :
    ((Matrix.fromCols e (μ • e')).submatrix id finSumFinEquiv.symm)ᴴ * G *
        (Matrix.fromCols e (μ • e')).submatrix id finSumFinEquiv.symm = μ • blk4 0 1 (-1) 0 := by
  have h : (Matrix.fromCols e (μ • e'))ᴴ * G * Matrix.fromCols e (μ • e') = μ • Matrix.fromBlocks 0 1 (-1) 0 := by
    rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols,
      Matrix.conjTranspose_smul, hμ, Matrix.fromBlocks_smul]
    simp only [Matrix.smul_mul, Matrix.mul_smul, h₁, h₂, h₃, h₄, smul_zero, smul_neg, neg_smul, Matrix.neg_mul, neg_zero]
  ext i j
  exact congrFun (congrFun h (finSumFinEquiv.symm i)) (finSumFinEquiv.symm j)

theorem fromRows_mul_fromCols_smul (G : Matrix (Fin (n + n)) (Fin (n + n)) E) (e e' : Matrix (Fin (n + n)) (Fin n) E)
    (μ : E) (hμ : μ ≠ 0) (h₁ : eᴴ * G * e = 0) (h₂ : e'ᴴ * G * e' = 0) (h₃ : e'ᴴ * G * e = 1) (h₄ : eᴴ * G * e' = 1) :
    (Matrix.fromRows (e'ᴴ * G) (μ⁻¹ • (eᴴ * G))).submatrix finSumFinEquiv.symm id *
        (Matrix.fromCols e (μ • e')).submatrix id finSumFinEquiv.symm = (1 : Matrix (Fin (n + n)) (Fin (n + n)) E) := by
  have h : Matrix.fromRows (e'ᴴ * G) (μ⁻¹ • (eᴴ * G)) * Matrix.fromCols e (μ • e') = 1 := by
    rw [Matrix.fromRows_mul_fromCols]
    simp only [Matrix.smul_mul, Matrix.mul_smul, h₁, h₂, h₃, h₄, smul_zero, smul_smul, mul_inv_cancel₀ hμ,
      one_smul, Matrix.fromBlocks_one]
  rw [← Matrix.submatrix_one_equiv (finSumFinEquiv (m := n) (n := n)).symm, ← h]
  rfl

end General

theorem Tm_gram_inv : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → (Tm A μ)ᴴ * (dblSp A).gram * Tm A μ = μ • Jst D A.rank ∧ IsUnit (Tm A μ).det ∧ (Tm A μ)⁻¹ = (Matrix.fromRows (dblDec A).qX (μ⁻¹ • (dblDec A).qY)).submatrix finSumFinEquiv.symm id := by
  intro D A μ hμ
  have h₄ : (dblDec A).eᴴ * (dblSp A).gram * (dblDec A).e' = 1 := by
    have := congrArg Matrix.conjTranspose (dblDec A).e'e
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, gram_conjTranspose,
      Matrix.conjTranspose_one, ← Matrix.mul_assoc] at this
  have hi := fromRows_mul_fromCols_smul (n := A.rank) (dblSp A).gram (dblDec A).e (dblDec A).e' μ hμ.1
    (dblDec A).ee (dblDec A).e'e' (dblDec A).e'e h₄
  exact ⟨gram_fromCols_smul (n := A.rank) (dblSp A).gram (dblDec A).e (dblDec A).e' μ hμ.2
    (dblDec A).ee (dblDec A).e'e' (dblDec A).e'e h₄, Matrix.isUnit_det_of_left_inverse hi, Matrix.inv_eq_left_inv hi⟩

end GlobalTheory.StdUnn
