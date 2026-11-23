import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableGx

noncomputable section

open MeasureTheory Matrix Filter Topology
open Ad3 Ad3.K Ad3.K.LC Ad3.K.LC.C

namespace GlobalTheory.CompanionTheory.PuBndC

def Vw (σ : ℝ) (T : ℂ) : ℝ := ‖T‖ ^ (-2 * σ) * (1 + |Real.log (‖T‖ ^ 2)|) / (1 + ‖T‖ ^ 2) ^ 2

def Bh (σ : ℝ) (h : M22) : ℝ :=
  ‖h 0 0‖ ^ (-2 * σ - 4) * Vw σ ((Matrix.of h).det / h 0 0 ^ 2) / ((1 + ‖h 0 0‖) ^ 3 * (1 + ‖h 0 1‖) ^ 3)

end GlobalTheory.CompanionTheory.PuBndC
