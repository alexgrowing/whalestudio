import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockMapFrameRestrictionRegular
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.UpVApply
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockMap_frame_restriction_regular : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)), IsBlockMap κ v → (∀ k, k ∈ Set.range κ ↔ ((∀ p, M.blk p ≠ some k) ∨ ∃ p, keep p ∧ M.blk p = some k)) → ∀ (F : FrameData ι Ψ N M.Ω M.blk) (z : (Σ k, ιk k) → ℂ), M.IsFrame F → z ∈ mcPts (mCoordIdeal (y ∘ v)) → M.GoodAt F (mCoordIdeal (pBase M v z)) → (∀ k, pBase M v z ⟨k, F.c k⟩ = 1) → ∃ H : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ, IsBlockDiag j (H τ) ∧ (H τ).det ≠ 0) ∧ ∀ p k, keep p → M.blk p = some k → ∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k, upV v z ⟨k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (pBase M v z) * minorIJ (H p.1) I (stepCols N j p.2) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.PFl.Fwd.main | exact GlobalTheory.CompanionTheory.Ar.PB.PFl.Fwd.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.PFl.Fwd.main <;> assumption)
