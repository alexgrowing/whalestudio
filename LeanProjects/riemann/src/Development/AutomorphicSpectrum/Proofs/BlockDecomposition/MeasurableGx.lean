import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.GammaSplitting.UnipotentTateFunctionalEquation

noncomputable section

open MeasureTheory Matrix Filter Topology
open Ad3 Ad3.K Ad3.K.LC Ad3.K.LC.C

namespace GlobalTheory.CompanionTheory.PuBndC

def rr (h : M22) : ℝ := ‖h 0 0‖ ^ 2 + ‖h 1 0‖ ^ 2

def dd (h : M22) : ℝ := ‖(Matrix.of h).det‖

def yy (h : M22) : ℝ := dd h ^ 2 / rr h ^ 2

def Fh (σ : ℝ) (h : M22) : ℝ :=
  rr h ^ (σ - 2) * dd h ^ (-2 * σ) * (1 + |Real.log (yy h)|) / ((1 + yy h) ^ 2 * (1 + ‖h‖) ^ 6)

def Sx (h : M22) (x : Fin 2 → ℂ) : ℝ :=
  1 + ‖h 0 0 * x 0 + h 0 1 * x 1‖ + ‖h 1 0 * x 0 + h 1 1 * x 1‖

def gx (σ : ℝ) (h : M22) (x : Fin 2 → ℂ) : ℝ := ‖x 1‖ ^ (2 * σ - 2) / Sx h x ^ 6

def Ah (h : M22) : ℝ := (rr h)⁻¹ * (1 + |Real.log (yy h)|) / ((1 + yy h) ^ 2 * (1 + ‖h‖) ^ 6)

end GlobalTheory.CompanionTheory.PuBndC
