import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAntiInvolutionOfChars
import Formalism.LocalToGlobal.IndefiniteReal.Bridge
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
open Formalism.IndefR.Bridge Formalism.L2.DIV Formalism.DivisionValues Formalism.L2.Col NumberField MeasureTheory Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_anti_involution_of_chars : ∀ {G W : Type} [Group G] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (J L : Subgroup G) (χ : J →* ℂˣ) (x y : G) (A B A' : Finset G) (F : G → W), (∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ L ∧ k = k₁ * k₂ ∧ ∀ l ∈ L, Commute k₂ l) → (∀ k : J, (k : G) ∈ L → χ k = 1) → (∃ θ : G → G, (∀ g ∈ L, θ g ∈ L) ∧ (∀ x ∈ L, ∀ y ∈ L, θ (x * y) = θ y * θ x) ∧ (∀ x ∈ L, θ (θ x) = x) ∧ (∀ k ∈ J ⊓ L, θ k ∈ J) ∧ ∀ g ∈ L, ∃ a ∈ J ⊓ L, ∃ b ∈ J ⊓ L, θ g = a * g * b) → (∀ a ∈ A, a ∈ L) → (∀ a ∈ B, a ∈ L) → (∀ a ∈ A', a ∈ L) → IsDC J x A → IsDC J y B → IsDC J x⁻¹ A' → (∀ (k : J) (h : G), F (h * k) = (χ k : ℂ) • F h) → dcOp A (dcOp B F) = dcOp B (dcOp A F) ∧ A.card = A'.card := by
  first | exact @GlobalTheory.DoubleCosetComm.dcOp_comm_and_card | exact GlobalTheory.DoubleCosetComm.dcOp_comm_and_card | (intros; apply GlobalTheory.DoubleCosetComm.dcOp_comm_and_card <;> assumption)
