import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJMatrixSchwartz
import GroundTheory.AutomorphicForms.CuspidalDiscreteness

open MeasureTheory NumberField ComplexConjugate
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace GJGlobal

open Reduction RightCosetSpace

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

def ratMat (ξ : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) 𝔸[K] :=
  ξ.map (algebraMap K 𝔸[K])

theorem ratMat_mul (ξ η : Matrix (Fin n) (Fin n) K) : ratMat (ξ * η) = ratMat ξ * ratMat η :=
  Matrix.map_mul

theorem coe_diagonal (γ : GL (Fin n) K) :
    ((AdelicGLn.diagonal K n γ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) =
      ratMat (γ : Matrix (Fin n) (Fin n) K) := by
  ext i j
  rw [AdelicGLn.diagonal_apply]
  rfl

variable (μ : Measure (normOneGL K n))

def matrixCoeff (φ₁ φ₂ : AdelicGLn.AdelicGL K n → ℂ) (g : AdelicGLn.AdelicGL K n) : ℂ :=
  ∫ x in fundamentalDomain (rationalGLOne K n), φ₁ ((x : AdelicGLn.AdelicGL K n) * g) *
    conj (φ₂ (x : AdelicGLn.AdelicGL K n)) ∂μ

def detPow (g : AdelicGLn.AdelicGL K n) (s : ℂ) : ℂ :=
  ((detModule K n g : ℝ) : ℂ) ^ s

def zetaIntegrand (Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ) (f : AdelicGLn.AdelicGL K n → ℂ) (s : ℂ)
    (g : AdelicGLn.AdelicGL K n) : ℂ :=
  Φ (g : Matrix (Fin n) (Fin n) 𝔸[K]) * f g * detPow g (s + ((n : ℂ) - 1) / 2)

def globalZeta (ν : Measure (AdelicGLn.AdelicGL K n)) (Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ)
    (f : AdelicGLn.AdelicGL K n → ℂ) (s : ℂ) : ℂ :=
  ∫ g, zetaIntegrand Φ f s g ∂ν

def thetaPairing (φ₁ φ₂ Ξ : AdelicGLn.AdelicGL K n → ℂ) (t : {r : ℝ // 0 < r}) : ℂ :=
  ∫ x in fundamentalDomain (rationalGLOne K n), ∫ y in fundamentalDomain (rationalGLOne K n),
    conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * φ₁ (y : AdelicGLn.AdelicGL K n) *
      ∑' γ : GL (Fin n) K, Ξ (centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ *
        AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n)) ∂μ ∂μ

end GJGlobal

end

end GroundTheory.Automorphic
