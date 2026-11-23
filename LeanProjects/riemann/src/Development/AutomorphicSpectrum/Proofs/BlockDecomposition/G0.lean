import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.UnipotentTateFunctionalEquation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.FunctionalEquationGL2GL1Complex

noncomputable section

open MeasureTheory
open Ad3 Ad3.LR Ad3.LR.C

namespace GlobalTheory.CompanionTheory.PuBnd

def Wt (N : ℕ) (h : M22) (x : Fin 2 → ℝ) : ℝ :=
  1 / (1 + ‖h‖ + |h 0 0 * x 0 + h 0 1 * x 1| + |h 1 0 * x 0 + h 1 1 * x 1|) ^ N

def Ew (k : ℕ) (D R : ℝ) : ℝ :=
  (|D| / R) ^ ((2 * (k : ℝ) - 1) / 2) * Real.exp (-(2 * Real.pi * |D| / R))

def V (k : ℕ) (σ T : ℝ) : ℝ := |T| ^ ((k : ℝ) - 1 - σ) * Real.exp (-(Real.pi * |T|))

def G0 (k : ℕ) (σ a b c d : ℝ) : ℝ :=
  |a| ^ (-2 - σ) / ((1 + |a|) ^ 2 * (1 + |b|) ^ 2) * V k σ ((d - c * b / a) / a)

def Gi (k : ℕ) (σ : ℝ) (q : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  if |q.2.1| ≤ |q.1.1| then G0 k σ q.1.1 q.1.2 q.2.1 q.2.2 else 0

end GlobalTheory.CompanionTheory.PuBnd
