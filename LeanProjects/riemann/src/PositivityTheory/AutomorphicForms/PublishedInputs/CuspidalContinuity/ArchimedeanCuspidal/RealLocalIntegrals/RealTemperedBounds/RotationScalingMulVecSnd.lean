import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealTemperedBounds.StepsD
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightVectorExplicitFormula

noncomputable section

open MeasureTheory Matrix Complex

namespace Ad3.LR.DK

def al (h : M22) : ℂ := (h 0 0 : ℂ) + (h 1 0 : ℂ) * I

def sq4 (h : M22) : ℝ := ∑ r, ∑ c, h r c ^ 2

def Gc (k : ℕ) (c0 c1 : Fin 2 → ℝ) : ℂ :=
  if 0 < c0 0 * c1 1 - c1 0 * c0 1 then
    (((c0 0 * c1 1 - c1 0 * c0 1 : ℝ)) : ℂ) ^ (k - 2) *
      cexp (2 * Real.pi * I * (((c1 0 : ℂ) + (c1 1 : ℂ) * I) / ((c0 0 : ℂ) + (c0 1 : ℂ) * I)) -
        Real.pi * ((c0 0 ^ 2 + c0 1 ^ 2 + c1 0 ^ 2 + c1 1 ^ 2 : ℝ) : ℂ) -
        Real.pi * (((c0 0 ^ 2 + c0 1 ^ 2) / (c0 0 * c1 1 - c1 0 * c0 1) ^ 2 : ℝ) : ℂ))
  else 0

def Mc (c0 : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![c0 0, -c0 1; c0 1, c0 0]

def Fr (k : ℕ) (s t : ℝ) : ℝ :=
  if 0 < t then (s * t) ^ (k - 2) * s⁻¹ ^ (1 / 2 : ℝ) *
    Real.exp (-2 * Real.pi * t - Real.pi * s - Real.pi * s * t ^ 2 - Real.pi / (s * t ^ 2) - Real.pi / s)
  else 0

def colE : M22 ≃ᵐ (Fin 2 → ℝ) × (Fin 2 → ℝ) :=
  (MeasurableEquiv.piCongrRight (fun _ : Fin 2 => MeasurableEquiv.finTwoArrow)).trans
    (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin 2))

def sI (k : ℕ) (Φ : Sw) (h : M22) : ℂ :=
  Wm k (Matrix.of h)⁻¹ * inn Φ 1 (Matrix.of h) * sg (Matrix.of h).det *
    ((|(Matrix.of h).det| ^ (-(1 : ℝ) / 2) : ℝ) : ℂ)

end Ad3.LR.DK

namespace Ad3.LR

open DK

end Ad3.LR
