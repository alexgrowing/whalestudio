import Mathlib

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.RLT

open MeasureTheory

def qv (a b t : ℝ) : ℝ := (t + a) ^ 2 + b ^ 2

def fF (y a b σ t : ℝ) : ℝ := y ^ σ * qv a b t ^ (-σ)

def fF' (y a b σ t : ℝ) : ℝ := -2 * σ * y ^ σ * (t + a) * qv a b t ^ (-σ - 1)

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.RLT
