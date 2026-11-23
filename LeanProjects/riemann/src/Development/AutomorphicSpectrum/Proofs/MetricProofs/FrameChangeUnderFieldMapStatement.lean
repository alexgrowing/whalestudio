import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameChangeUnderFieldMap
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsImg
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AevalNeZeroOfNotMem
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsValueAtOfTorus
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsBlkCover
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJMap
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishingStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPointsStatement
import GroundTheory.HeightsAndTheta.Heights.Intersections.PtsOverPt
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_change_under_field_map : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)] (Ω₂ : Type) [Field Ω₂] (x₂ : (Σ k, ι₂ k) → Ω₂) (φ : M.Ω →+* Ω₂) (zb : (Σ k, ι₂ k) → ℂ) (F₁ F₂ : FrameData ι Ψ N M.Ω M.blk), zb ∈ mcPts (mCoordIdeal x₂) → M.IsFrame F₁ → M.IsFrame F₂ → (∀ k, M.x ⟨k, F₁.c k⟩ ≠ 0) → (∀ k, M.x ⟨k, F₂.c k⟩ ≠ 0) → ∀ (p : Ψ × Fin N) (k : K), M.blk p = some k → (∀ (m : ι k) (I : Finset (Fin N)), RegAt x₂ (mCoordIdeal zb) (φ (F₁.u ⟨k, m⟩ I)) ∧ RegAt x₂ (mCoordIdeal zb) (φ (F₂.u ⟨k, m⟩ I)) ∧ RegAt x₂ (mCoordIdeal zb) (φ (F₁.u' I ⟨k, m⟩)) ∧ RegAt x₂ (mCoordIdeal zb) (φ (F₂.u' I ⟨k, m⟩))) → (∀ a b, RegAt x₂ (mCoordIdeal zb) ((((F₁.T p.1).map φ)⁻¹ * (F₂.T p.1).map φ) a b) ∧ RegAt x₂ (mCoordIdeal zb) ((((F₂.T p.1).map φ)⁻¹ * (F₁.T p.1).map φ) a b)) → ∃ c : ℂ, c ≠ 0 ∧ ∀ h : Matrix (Fin N) (Fin N) ℂ, IsBlockDiag j h → ∀ m : ι k, ∑ I, valAt x₂ (φ (F₁.u ⟨k, m⟩ I)) zb * minorIJ (CovMap.LocImg.valMat x₂ zb (((F₁.T p.1).map φ)⁻¹ * (F₂.T p.1).map φ) * h) I (stepCols N j p.2) = c * ∑ I, valAt x₂ (φ (F₂.u ⟨k, m⟩ I)) zb * minorIJ h I (stepCols N j p.2) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.FV.main | exact GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.FV.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.FV.main <;> assumption)
