import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.ExplicitConstants.UniformIffAboveThreshold
import Mathlib

open Filter Set Real

namespace KStar.Consta.Params

variable (P : Params)

noncomputable def L1 (k x : ℝ) (p : ℕ) : ℕ := ⌈Real.logb p ((k * x ^ Aexp) ^ 4)⌉₊

noncomputable def L2 (k x : ℝ) (S : Set ℕ) : ℕ := 2 * sSup (L1 k x '' S)

noncomputable def CT (o : ℕ) : ℝ := 2 * o * ((2 : ℝ) ^ P.Lbar + 2)

end KStar.Consta.Params
