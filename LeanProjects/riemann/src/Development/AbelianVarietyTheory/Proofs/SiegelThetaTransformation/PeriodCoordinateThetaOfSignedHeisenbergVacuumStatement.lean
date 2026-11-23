import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PeriodCoordinateThetaOfSignedHeisenbergVacuum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodCoordinateTheta_of_signedHeisenbergVacuum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L : Lt E r, SelfD X L → ∀ v : TF n g, IsVac X bas w (tens (stdL E n) L) v → ∀ b : Fin g ⊕ Fin g → (Fin r → E), (∀ u, u ∈ L ↔ ∃ m : Fin g ⊕ Fin g → ℤ, u = ∑ j, m j • b j) → (∀ i j, EF X (b i) (b j) = -(omegaStd (Pi.single i 1) (Pi.single j 1) : ℤ)) → ∃ (c₁ c₂ : Fin g → ℂ) (C : ℂ), C ≠ 0 ∧ (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) ∧ (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) ∧ ∀ x ∈ X.dom, ∀ h τ : Matrix (Fin g) (Fin g) ℂ, h = (Matrix.of fun i k => pv X idx x (b (Sum.inl k)) i)⁻¹ → τ = h * (Matrix.of fun i k => pv X idx x (b (Sum.inr k)) i) → IsUnit h.det ∧ τ ∈ SW.Siegel (Fin g) ∧ (∀ z w' : Fin g → ℂ, hx X bas idx x z w' = (h *ᵥ z) ⬝ᵥ ((τ.map Complex.im)⁻¹.map fun t : ℝ => (t : ℂ)) *ᵥ star (h *ᵥ w')) ∧ (∀ i, eps1 X w (b (Sum.inl i)) = cexp (2 * Real.pi * I * c₁ i) ∧ eps1 X w (b (Sum.inr i)) = cexp (2 * Real.pi * I * c₂ i)) ∧ ∀ z : Fin n → Fin g → ℂ, thA X bas idx v x z = C * h.det ^ (n / 2) * ∏ k, (cexp (Real.pi / 2 * ((h *ᵥ z k) ⬝ᵥ ((τ.map Complex.im)⁻¹.map fun t : ℝ => (t : ℂ)) *ᵥ (h *ᵥ z k))) * thetaChar τ c₁ c₂ (h *ᵥ z k)) := by
  first | exact @GlobalTheory.Dict.VacForm.thA_vacuum | exact GlobalTheory.Dict.VacForm.thA_vacuum | (intros; apply GlobalTheory.Dict.VacForm.thA_vacuum <;> assumption)
