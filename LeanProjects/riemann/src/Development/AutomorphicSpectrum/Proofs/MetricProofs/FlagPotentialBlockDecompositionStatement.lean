import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPotentialBlockDecomposition
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_potential_block_decomposition : ∀ (N j : ℕ) (i : Fin N) (Pi G h : Matrix (Fin N) (Fin N) ℂ), j ≤ N → IsPeriodGram j Pi G → IsBlockDiag j G → G.PosDef → IsBlockDiag j h → h.det ≠ 0 → InFlagDomain N j (Pi * h) ∧ stepPot N j i (Pi * h) = blockPot j i G h + Real.log ‖detFac j i h‖ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.stepPot_mul_eq_blockPot | exact GlobalTheory.CompanionTheory.Ar.PB.stepPot_mul_eq_blockPot | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.stepPot_mul_eq_blockPot <;> assumption)
