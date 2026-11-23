import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicFramesSamePeriodCoordinates
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsGenericComponentPointsOffMeagre
open NumberField
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphicFrames_same_periodCoordinates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (B : Set ℂ) (x₁ : ℂ → Frame X.Ψ r), (∀ w ∈ B, x₁ w ∈ X.dom) → (∀ v ∈ X.Λ, ∀ τ a, DifferentiableOn ℂ (fun w => GlobalTheory.GenericFrames.pc X (x₁ w) v τ a) B) → ∃ x : ℂ → Frame X.Ψ r, DifferentiableOn ℂ x B ∧ ∀ w ∈ B, x w ∈ X.dom ∧ ∀ v τ a, GlobalTheory.GenericFrames.pc X (x w) v τ a = GlobalTheory.GenericFrames.pc X (x₁ w) v τ a := by
  first | exact @GlobalTheory.HolFrameLift.exists_holomorphic_frames | exact GlobalTheory.HolFrameLift.exists_holomorphic_frames | (intros; apply GlobalTheory.HolFrameLift.exists_holomorphic_frames <;> assumption)
