import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockMinorSumFrameIdentity
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TransPtBase
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_minor_sum_frame_identity : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (S : Type) [CommRing S] (ρ : M.Ω →+* S) (F : FrameData ι Ψ N M.Ω M.blk), M.IsFrame F → ∀ (p : Ψ × Fin N) (k : K), M.blk p = some k → ∀ (m : ι k) (h : Matrix (Fin N) (Fin N) S), IsBlockDiag j h → detFac j p.2 ((F.T p.1).map ρ) * ∑ I, ρ (M.coef ⟨k, m⟩ I) * minorIJ ((F.T p.1).map ρ * h) I (stepCols N j p.2) = ρ (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k') * ∑ I, ρ (F.u ⟨k, m⟩ I) * minorIJ h I (stepCols N j p.2) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovGraph.FrameExt.frame_identity_map | exact GlobalTheory.CompanionTheory.Ar.PB.CovGraph.FrameExt.frame_identity_map | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovGraph.FrameExt.frame_identity_map <;> assumption)
