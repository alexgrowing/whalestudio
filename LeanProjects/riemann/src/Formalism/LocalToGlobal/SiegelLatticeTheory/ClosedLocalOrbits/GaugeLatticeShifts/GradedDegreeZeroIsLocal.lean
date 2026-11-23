import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LintegralMulRightOfMap

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal ComplexConjugate
open Matrix

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

abbrev MZ (r : ℕ) : Type := Fin (r + 1) → Fin (r + 1) → ℂ

abbrev UC (r : ℕ) : Type := {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → ℂ

def upMat {r : ℕ} (y : UC r) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  Matrix.of fun a b => if a = b then 1 else if h : a < b then y ⟨(a, b), h⟩ else 0

def GradedDegreeZeroIsLocal {n r : ℕ} (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : Set (Formalism.REAL.UJ ε) :=
  {g | (∀ a, uMat g *ᵥ e a = e a) ∧ uMat g *ᵥ z = z}

def SSplit : Prop :=
  ∀ (n r k : ℕ) (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (T T' sc : ℝ),
    FrameLoc ε k e z z' T T' → 0 < sc →
    ∀ μS : Measure (Formalism.REAL.UJ ε), IsHaarS (SLoc ε e z) μS →
    ∃ μ0 : Measure (Formalism.REAL.UJ ε), IsHaarS (GradedDegreeZeroIsLocal ε e z) μ0 ∧
    ∃ σ : UC r → Formalism.REAL.UJ ε, Measurable σ ∧ (∀ y, σ y ∈ SLoc ε e z) ∧
      (∀ y b, uMat (σ y)⁻¹ *ᵥ famSc sc e z b = ∑ a, upMat y a b • famSc sc e z a) ∧
      ∀ f : Formalism.REAL.UJ ε → ℝ≥0∞, Measurable f →
        ∫⁻ s, f s ∂μS = ∫⁻ y, ∫⁻ s₀, f (s₀ * σ y) ∂μ0 ∂(volume : Measure (UC r))

def ZAct : Prop :=
  ∀ (n r : ℕ) (ε : Fin n → Bool) (f f' : Fin (r + 1) → Fin n → ℂ) (s s' g : Formalism.REAL.UJ ε)
    (P P' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ),
    (∀ b, uMat s⁻¹ *ᵥ f b = ∑ a, P a b • f a) → (∀ b, uMat s'⁻¹ *ᵥ f' b = ∑ a, P' a b • f' a) →
    Zhat ε f f' (uMat (s * g * s'⁻¹)) = Pᴴ * Zhat ε f f' (uMat g) * P'

def DlLDU : Prop :=
  ∀ (r : ℕ) (x y : UC r) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (l : ℕ),
    Dl ((upMat x)ᴴ * Z * upMat y) l = Dl Z l

def LDUJac : Prop :=
  ∀ r : ℕ,
    (∀ ψ : MZ r → ℝ≥0∞, Measurable ψ →
      ∫⁻ Z, ψ Z ∂(volume : Measure (MZ r)) =
        ∫⁻ x : UC r, ∫⁻ c : Fin (r + 1) → ℂ, ∫⁻ y : UC r,
          ENNReal.ofReal (JacV (Matrix.diagonal c)) * ψ ((upMat x)ᴴ * Matrix.diagonal c * upMat y)) ∧
    (∀ Z : MZ r, BigCell Z → ∃ (x : UC r) (c : Fin (r + 1) → ℂ) (y : UC r), (∀ l, c l ≠ 0) ∧
      (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) = (upMat x)ᴴ * Matrix.diagonal c * upMat y) ∧
    ∃ q : MZ r → UC r × (Fin (r + 1) → ℂ) × UC r, Measurable q ∧
      ∀ x c y, (∀ l, c l ≠ 0) → q ((upMat x)ᴴ * Matrix.diagonal c * upMat y) = (x, c, y)

def ZDisint : Prop :=
  ∀ (n r k : ℕ) (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (T T' sc : ℝ),
    FrameLoc ε k e z z' T T' → 0 < sc →
    ∀ μ0 μ0' : Measure (Formalism.REAL.UJ ε), IsHaarS (GradedDegreeZeroIsLocal ε e z) μ0 → IsHaarS (GradedDegreeZeroIsLocal ε e z') μ0' →
    ∃ C, 0 < C ∧ ∀ g : MZ r → Formalism.REAL.UJ ε, Measurable g →
      (∀ Z : MZ r, BigCell Z → 0 < Gv T T' Z → ZLoc ε sc e z z' (g Z) = Z) →
      ∀ φ : Formalism.REAL.UJ ε → ℝ≥0∞, Measurable φ →
        ∫⁻ x, φ x ∂(Formalism.REAL.muG ε) =
          ∫⁻ Z in {Z : MZ r | BigCell Z ∧ 0 < Gv T T' Z}, ENNReal.ofReal (C * Gv T T' Z ^ (k - 1)) *
            ∫⁻ s, ∫⁻ s', φ (s * g Z * s'⁻¹) ∂μ0' ∂μ0

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL
