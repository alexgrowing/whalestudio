import Mathlib

noncomputable section

namespace Formalism.L2.S.S7.PositiveOrthantChangeOfVariables

open MeasureTheory Set
open scoped ENNReal

def posO (a : ℕ) : Set (Fin a → ℝ) := Set.univ.pi fun _ => Set.Ioi (0 : ℝ)

def chv {a : ℕ} (e : Fin a → ℝ) (t : Fin a → ℝ) : Fin a → ℝ := fun i => t i ^ (-(e i)⁻¹)

def chvD {a : ℕ} (e : Fin a → ℝ) (t : Fin a → ℝ) : (Fin a → ℝ) →L[ℝ] (Fin a → ℝ) :=
  ContinuousLinearMap.pi fun i => ((-(e i)⁻¹) * t i ^ (-(e i)⁻¹ - 1)) • ContinuousLinearMap.proj i

end Formalism.L2.S.S7.PositiveOrthantChangeOfVariables

end
