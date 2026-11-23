import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealTemperedBounds.TrDefs
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealSharpBounds.HasFDerivAtPm

noncomputable section

open MeasureTheory Matrix Ad3.LR Ad3.LR.DTr

namespace GlobalTheory.CompanionTheory.DInt2

def al (h : M22) : ℂ := (h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I

def be (h : M22) : ℂ := (h 0 1 : ℂ) + (h 1 1 : ℂ) * Complex.I

def dd (h X : M22) : ℝ := X 0 0 * h 1 1 + h 0 0 * X 1 1 - X 0 1 * h 1 0 - h 0 1 * X 1 0

def uu (h : M22) : ℝ := (Matrix.of h).det / ‖al h‖ ^ 2

def tt (h : M22) : ℂ := (((Matrix.of h).det : ℝ) : ℂ) / al h ^ 2

def rho (c d : Fin 2) (h : M22) : ℂ := al (rpol c d h) / al h

def kap (a b : Fin 2) : ℂ := (if b = 0 then 1 else Complex.I) * (if a = 0 then -Complex.I else 1)

def ell (k : ℕ) (h X : M22) : ℂ :=
  ((k : ℂ) - 1) * (dd h X : ℂ) / (((Matrix.of h).det : ℝ) : ℂ) + (1 - 2 * (k : ℂ)) * al X / al h +
    2 * Real.pi * Complex.I * (be X * al h - be h * al X) / al h ^ 2

def Qf (k : ℕ) (v : ℂ) (c d : Fin 2) (h : M22) : ℂ :=
  (if c = d then v - 2 - ((k : ℂ) - 1) else 0) + (2 * (k : ℂ) - 1) * rho c d h -
    2 * Real.pi * Complex.I * kap c d * tt h

end GlobalTheory.CompanionTheory.DInt2
