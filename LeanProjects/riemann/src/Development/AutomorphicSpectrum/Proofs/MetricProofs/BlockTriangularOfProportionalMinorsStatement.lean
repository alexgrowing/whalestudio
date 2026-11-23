import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockTriangularOfProportionalMinors
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsLocSec
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJMap
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_triangular_of_proportional_minors : ∀ (N j : ℕ) (h g : Matrix (Fin N) (Fin N) ℂ), j ≤ N → IsBlockDiag j h → IsBlockDiag j g → h.det ≠ 0 → g.det ≠ 0 → (∀ i : Fin N, IsProperStep N j i → ∃ μ : ℂ, ∀ I, minorIJ g I (stepCols N j i) = μ * minorIJ h I (stepCols N j i)) → (h⁻¹ * g).BlockTriangular id := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.TriStep.triangular_of_minors_proportional | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.TriStep.triangular_of_minors_proportional | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.TriStep.triangular_of_minors_proportional <;> assumption)
