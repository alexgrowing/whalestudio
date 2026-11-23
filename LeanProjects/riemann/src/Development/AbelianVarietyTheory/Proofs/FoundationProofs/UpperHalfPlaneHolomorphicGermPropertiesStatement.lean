import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneHolomorphicGermProperties
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties : (∀ a b : ℂ → ℂ, DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs → (((a : Mero) = (b : Mero)) ↔ ∀ z ∈ Hs, a z = b z)) ∧ (∀ a b : ℂ → ℂ, DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs → (∀ z ∈ Hs, a z * b z = 0) → (∀ z ∈ Hs, a z = 0) ∨ (∀ z ∈ Hs, b z = 0)) ∧ (∀ (g : GQ) (φ ψ : ℂ → ℂ), (φ : Mero) = (ψ : Mero) → ((fun z => φ (mob g z) : ℂ → ℂ) : Mero) = ((fun z => ψ (mob g z) : ℂ → ℂ) : Mero)) ∧ (∀ (φ ψ : ℂ → ℂ), (φ : Mero) = (ψ : Mero) → ∀ τ ∈ Hs, ∀ᶠ z in nhdsWithin τ {τ}ᶜ, φ z = ψ z) ∧ (∀ (m : ℕ) (a b : ℂ → ℂ), 0 < m → DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs → (∀ z ∈ Hs, a z ^ m = b z ^ m) → ∃ k : ℕ, ∀ z ∈ Hs, a z = Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) / (m : ℂ)) * b z) := by
  first | exact @GlobalTheory.KZ.Germ.main | exact GlobalTheory.KZ.Germ.main | (intros; apply GlobalTheory.KZ.Germ.main <;> assumption)
