import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableBoundedMulWeightFive

open MeasureTheory Matrix Filter Topology
open Ad3 Ad3.K Ad3.K.LC Ad3.K.LC.C GlobalTheory.CompanionTheory.ParsC

noncomputable section

namespace GlobalTheory.CompanionTheory.ParsC.Fib

def J : ℝ := ∫ w : ℂ, ((1 + ‖w‖) ^ 5)⁻¹

end GlobalTheory.CompanionTheory.ParsC.Fib
