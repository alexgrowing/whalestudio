import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.RadialIntegralLemmas
open UpperTheory.Esk

def F (k : ℕ) (g : GL (Fin 2) ℝ) (z : P) : ℂ := q1 k z (g • z) * j1 k g z

def U (k : ℕ) (g : GL (Fin 2) ℝ) (z : P) : ℂ := if 0 < z.1.im then F k g z else 0

def eta (a b : ℝ) : ℂ := ((a : ℂ) - b * Complex.I) / (Real.sqrt (a ^ 2 + b ^ 2) : ℂ)

end UpperTheory.Esk.RadialIntegralLemmas
