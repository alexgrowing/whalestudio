import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaCharOffNeZeroDifferentiableQuasiPeriodic
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TopLeWchartNsmul
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames CategoryTheory.MonObj GlobalTheory.AbelianLetters
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaCharOff_ne_zero_differentiable_quasiPeriodic' : ∀ (g : ℕ) (S : Finset (Fin g)) (τ : Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ), τ.IsSymm → (τ.map Complex.im).PosDef → (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) → (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) → (∀ k ∈ S, c₁ k = 0) → thetaCharOff S τ c₁ c₂ ≠ 0 ∧ Differentiable ℂ (thetaCharOff S τ c₁ c₂) ∧ ∀ m n : Fin g → ℤ, (∀ k ∈ S, n k = 0) → ∃ a : ℂ, a ≠ 0 ∧ ∀ z, thetaCharOff S τ c₁ c₂ (z + ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)))) = a * Complex.exp (-(2 * Real.pi * Complex.I) * ((fun i => (n i : ℂ)) ⬝ᵥ z)) * thetaCharOff S τ c₁ c₂ z := by
  first | exact @GlobalTheory.ThetaBlock.thetaCharOff_ne_zero_differentiable_quasiPeriodic | exact GlobalTheory.ThetaBlock.thetaCharOff_ne_zero_differentiable_quasiPeriodic | (intros; apply GlobalTheory.ThetaBlock.thetaCharOff_ne_zero_differentiable_quasiPeriodic <;> assumption)
