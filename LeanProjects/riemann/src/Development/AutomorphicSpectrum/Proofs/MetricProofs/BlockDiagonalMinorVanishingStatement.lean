import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishing
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_diagonal_minor_vanishing : ∀ (R : Type) [CommRing R] (N j : ℕ) (i : Fin N), j ≤ N → (∀ (T h : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)), minorIJ (T * h) I J = ∑ I', minorIJ T I I' * minorIJ h I' J) ∧ (∀ (h : Matrix (Fin N) (Fin N) R) (I : Finset (Fin N)), IsBlockDiag j h → ¬ IsStepRows N j i I → minorIJ h I (stepCols N j i) = 0 ∨ stepCols N j i = ∅) ∧ (∀ (h bb : Matrix (Fin N) (Fin N) R) (I : Finset (Fin N)), IsBlockDiag j bb → bb.BlockTriangular id → minorIJ (h * bb) I (stepCols N j i) = minorIJ h I (stepCols N j i) * ∏ c ∈ stepCols N j i, bb c c) ∧ ∀ T h : Matrix (Fin N) (Fin N) R, IsBlockDiag j T → IsBlockDiag j h → IsBlockDiag j (T * h) ∧ detFac j i (T * h) = detFac j i T * detFac j i h := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.MinorCalc.minors_main | exact GlobalTheory.CompanionTheory.Ar.PB.MinorCalc.minors_main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.MinorCalc.minors_main <;> assumption)
