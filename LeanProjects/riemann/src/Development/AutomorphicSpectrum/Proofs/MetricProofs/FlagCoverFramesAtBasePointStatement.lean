import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverFramesAtBasePoint
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TransPtBase
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverBasePointRegularStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorOfRegularMatrixValueStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_cover_frames_at_base_point : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (zb : (Σ k, baseIdx ι' M'.blk k) → ℂ) (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk), zb ∈ mcPts (mCoordIdeal M'.x) → M'.IsFrame F' → M.IsFrame F → M'.GoodAt F' (mCoordIdeal zb) → M.GoodAt F (mCoordIdeal (zb ∘ Cv.v)) → ∀ (p : Ψ × Fin N) (q : Σ k, ι k) (r : Σ k, ι' k), RegAt M'.x (mCoordIdeal zb) (coE Cv F' F p q r) ∧ valAt M'.x (coE Cv F' F p q r) zb = ∑ I, ∑ I' ∈ Finset.univ.filter (IsStepRows N j p.2), valAt M.x (F.u q I) (zb ∘ Cv.v) * minorIJ (Cv.trans F' F zb p.1) I I' * valAt M'.x (F'.u' I' r) zb := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovGraph.coE_regAt_valAt | exact GlobalTheory.CompanionTheory.Ar.PB.CovGraph.coE_regAt_valAt | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovGraph.coE_regAt_valAt <;> assumption)
