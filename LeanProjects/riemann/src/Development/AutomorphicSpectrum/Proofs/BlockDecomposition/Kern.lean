import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.SmoothMajorants.Bounds

noncomputable section

open MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.MajC

def kern (s T₀ : ℝ) (z : ℂ) : ℝ := (‖z‖ ^ 2)⁻¹ * min ((‖z‖ / T₀) ^ s) ((T₀ / ‖z‖) ^ s)

def dt (h : Ad3.K.LC.M22) : ℝ := ‖(Matrix.of h).det‖

def col (h : Ad3.K.LC.M22) : ℝ := max ‖h 0 0‖ ‖h 1 0‖

def hm (ε : ℝ) (N : ℕ) (β : ℝ) (h : Ad3.K.LC.M22) : ℝ :=
  dt h ^ (-(2 + ε)) * col h ^ (-2 + 2 * ε) * ((1 + ‖h‖) ^ N)⁻¹ * ((1 + β * (col h / dt h)) ^ N)⁻¹

def swp (h : Ad3.K.LC.M22) : Ad3.K.LC.M22 := ![h 1, h 0]

def gm (ε β : ℝ) (m : ℕ) (h : Ad3.K.LC.M22) : ℝ :=
  if ‖h 1 0‖ ≤ ‖h 0 0‖ ∧ h 0 0 ≠ 0 then
    β ^ (-ε) * ‖h 0 0‖ ^ (-4 + ε) * ((1 + ‖h 0 0‖) ^ m)⁻¹ * ((1 + ‖h 0 1‖) ^ m)⁻¹ *
      kern ε β (h 1 1 - h 1 0 / h 0 0 * h 0 1)
  else 0

end GlobalTheory.CompanionTheory.MajC
