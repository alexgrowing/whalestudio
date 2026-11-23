import Mathlib

noncomputable section

namespace ReciprocityTheory.GeometryOfNumbersTheory

open MeasureTheory

def sqN {N : ℕ} (z : Fin N → ℂ) : ℝ :=
  ∑ i, ‖z i‖ ^ 2

def gaussC (N : ℕ) : Measure (Fin N → ℂ) :=
  volume.withDensity fun z => ENNReal.ofReal ((Real.pi ^ N)⁻¹ * Real.exp (-sqN z))

def sphProb (N : ℕ) : Measure (Fin N → ℂ) :=
  (gaussC N).map fun z => (((Real.sqrt (sqN z))⁻¹ : ℝ) : ℂ) • z

def monoC {N : ℕ} (a : Fin N → ℕ) (z : Fin N → ℂ) : ℂ :=
  ∏ i, z i ^ a i

def monoNormSq {D : ℕ} (a : Fin (D + 1) → ℕ) : ℝ :=
  ((∏ i, (a i).factorial : ℕ) : ℝ) * (D.factorial : ℝ) / (((∑ i, a i) + D).factorial : ℝ)

def chiP (D n : ℕ) : ℝ :=
  -(1 / 2) * ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) n, Real.log (monoNormSq a)

end ReciprocityTheory.GeometryOfNumbersTheory
