import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions

open Finset ArithmeticFunction Filter Topology MeasureTheory Asymptotics
open Formalism.HermitianLattices.GL2PrimeSums Formalism.HermitianLattices.GL2a2

noncomputable section

namespace GlobalTheory.Mem.An.PsiZero

def err (u : ℝ) : ℝ := (psumR (fun n => Λ n) u - u) / u ^ 2

end GlobalTheory.Mem.An.PsiZero
