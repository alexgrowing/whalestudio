import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlkFProperStepInjectiveBlockDiag
import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blkF_properStep_injective_blockDiag : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] (K₀ : Type), (∀ r, blkF Ψ p q K₀ r = none ↔ ¬ IsProperStep (p + q) p r.2) ∧ (∀ r r' k, blkF Ψ p q K₀ r = some k → blkF Ψ p q K₀ r' = some k → r = r') ∧ ∀ τ : Ψ, IsBlockDiag p (gMat p q Ω τ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.Blocks.blocks_main | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.Blocks.blocks_main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.Blocks.blocks_main <;> assumption)
