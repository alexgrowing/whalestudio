import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMeasurePreservingFrameChangeProportionalHe
import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProbabilityMeasureAutQuotientNormalized
open MeasureTheory Topology Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_measurePreserving_frameChange_proportional_hermitian : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (y : Frame X.Ψ r) (y' : Frame X'.Ψ r), X.Ψ = X'.Ψ → X.p0 = X'.p0 → y ∈ OrthFr X → y' ∈ OrthFr X' → (∀ (τ : X.Ψ), ∃ t : ℝ, t ≠ 0 ∧ X'.Gm.map τ.1 = (t : ℂ) • X.Gm.map τ.1) → ∃ (e : RealGrp X ≃ᵐ RealGrp X') (α : RealGrp X → RealGrp X) (u : RealGrp X), MeasurePreserving e (haarR X) (haarR X') ∧ Measurable α ∧ (∀ t, α (α t) = u⁻¹ * t * u) ∧ ∀ t (τ : X.Ψ) (τ' : X'.Ψ), τ.1 = τ'.1 → mat y' τ' * ((e (α t) τ' : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * (mat y' τ')⁻¹ = mat y τ * ((t τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * (mat y τ)⁻¹ := by
  first | exact @GlobalTheory.PeterssonFrameChange.frame_change | exact GlobalTheory.PeterssonFrameChange.frame_change | (intros; apply GlobalTheory.PeterssonFrameChange.frame_change <;> assumption)
