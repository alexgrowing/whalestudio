import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsLowerUniBlockDiagFactorization
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.UpVApply
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lowerUni_blockDiag_factorization : ∀ (N j : ℕ) (kp : Fin N → Prop) (G : Matrix (Fin N) (Fin N) ℂ), j ≤ N → IsBlockDiag j G → G.det ≠ 0 → (∀ i, kp i → IsProperStep N j i → minorIJ G (stepCols N j i) (stepCols N j i) ≠ 0) → ∃ L W : Matrix (Fin N) (Fin N) ℂ, IsBlockDiag j L ∧ IsLowerUni L ∧ (∀ a b : Fin N, b < a → ((a : ℕ) < N - j ↔ (b : ℕ) < N - j) → (¬ ∃ i, kp i ∧ IsProperStep N j i ∧ b ∈ stepCols N j i ∧ a ∉ stepCols N j i) → L a b = 0) ∧ IsBlockDiag j W ∧ (∀ i, kp i → IsProperStep N j i → ∀ c ∈ stepCols N j i, ∀ x, x ∉ stepCols N j i → W x c = 0) ∧ G * W = L := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.BigCellLU.exists_lu | exact GlobalTheory.CompanionTheory.Ar.PB.BigCellLU.exists_lu | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.BigCellLU.exists_lu <;> assumption)
