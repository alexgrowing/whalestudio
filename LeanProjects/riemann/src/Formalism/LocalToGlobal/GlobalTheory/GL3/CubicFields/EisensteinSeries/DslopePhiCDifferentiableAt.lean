import Mathlib

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.KroneckerLimitFormula

open Complex Asymptotics Filter Topology

def gC (y : ℝ) (s : ℂ) : ℂ :=
  2 * (y : ℂ) ^ (1 - s) * (Real.sqrt Real.pi : ℂ) * Gamma (s - 1 / 2) * (Gamma s)⁻¹

def PhiC (y : ℝ) (s : ℂ) : ℂ := gC y s * riemannZeta₁ (2 * s - 1) / 2

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.KroneckerLimitFormula

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
