import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.DetUpMatSub

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal ComplexConjugate
open Matrix

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

def mulU {r : ℕ} (a b : UC r) : UC r := fun p => (upMat a * upMat b) p.1.1 p.1.2

structure IsClSub {n : ℕ} {ε : Fin n → Bool} (H : Set (Formalism.REAL.UJ ε)) : Prop where
  one_mem : (1 : Formalism.REAL.UJ ε) ∈ H
  mul_mem : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H
  inv_mem : ∀ x ∈ H, x⁻¹ ∈ H
  closed : IsClosed H

def SSHaar : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Set (Formalism.REAL.UJ ε)), IsClSub H →
    (∃ μ, IsHaarS H μ) ∧
    ∀ μ m : Measure (Formalism.REAL.UJ ε), IsHaarS H μ → m Hᶜ = 0 → (∀ s ∈ H, m.map (fun x => s * x) = m) →
      IsFiniteMeasureOnCompacts m → ∃ c : ℝ≥0∞, c ≠ ∞ ∧ m = c • μ

def SSGrp : Prop :=
  ∀ (n r k : ℕ) (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (T T' : ℝ),
    FrameLoc ε k e z z' T T' → IsClSub (SLoc ε e z) ∧ IsClSub (GradedDegreeZeroIsLocal ε e z)

def SSSec : Prop :=
  ∀ (n r k : ℕ) (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (T T' sc : ℝ),
    FrameLoc ε k e z z' T T' → 0 < sc →
    ∃ σ : UC r → Formalism.REAL.UJ ε, Continuous σ ∧ (∀ y, σ y ∈ SLoc ε e z) ∧
      ∀ y b, uMat (σ y)⁻¹ *ᵥ famSc sc e z b = ∑ a, upMat y a b • famSc sc e z a

def SSCoord : Prop :=
  ∀ (n r k : ℕ) (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (T T' sc : ℝ),
    FrameLoc ε k e z z' T T' → 0 < sc →
    ∃ π : Formalism.REAL.UJ ε → UC r, Continuous π ∧
      (∀ g ∈ SLoc ε e z, ∀ y : UC r,
        (∀ b, uMat g⁻¹ *ᵥ famSc sc e z b = ∑ a, upMat y a b • famSc sc e z a) → π g = y) ∧
      (∀ g ∈ SLoc ε e z, ∀ h ∈ SLoc ε e z, π (g * h) = mulU (π h) (π g)) ∧
      (∀ g ∈ SLoc ε e z, ∀ h ∈ SLoc ε e z, π g = π h → g * h⁻¹ ∈ GradedDegreeZeroIsLocal ε e z) ∧
      (∀ g ∈ GradedDegreeZeroIsLocal ε e z, g ∈ SLoc ε e z ∧ π g = 0)

def SSBiInv0 : Prop :=
  ∀ (n r k : ℕ) (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (T T' : ℝ),
    FrameLoc ε k e z z' T T' →
    ∀ μ0 : Measure (Formalism.REAL.UJ ε), IsHaarS (GradedDegreeZeroIsLocal ε e z) μ0 →
    ∀ t ∈ SLoc ε e z, ∀ u ∈ SLoc ε e z, t * u ∈ GradedDegreeZeroIsLocal ε e z → μ0.map (fun x => t * x * u) = μ0

def SSLebU : Prop :=
  ∀ (r : ℕ) (b : UC r), MeasurePreserving (fun a : UC r => mulU a b) volume volume

theorem upMat_zero {r : ℕ} : upMat (0 : UC r) = 1 := by
  ext a b
  simp only [upMat, Matrix.of_apply, Pi.zero_apply, Matrix.one_apply]
  split_ifs <;> rfl

theorem mulU_zero {r : ℕ} (y : UC r) : mulU y 0 = y := by
  funext p
  simp only [mulU]
  rw [upMat_zero, Matrix.mul_one]
  simp only [upMat, Matrix.of_apply]
  rw [if_neg (ne_of_lt p.2), dif_pos p.2]

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL
