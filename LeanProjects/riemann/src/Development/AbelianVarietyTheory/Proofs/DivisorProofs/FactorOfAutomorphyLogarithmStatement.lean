import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorOfAutomorphyLogarithm
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factor_of_automorphy_logarithm : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ∀ (u : Fl g → Pt E g → ℂ), IsFactor B τ (stdLat g) u → (∀ b ∈ B, ∃ f : Fl g → (Fin g → ℂ) → ℂ, (∀ l ∈ stdLat g, Differentiable ℂ (f l) ∧ ∀ z, u l (b, z) = Complex.exp (2 * π * Complex.I * f l z)) ∧ ∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, ∀ z, f l (z + per (τ b) l') + f l' z - f l' (z + per (τ b) l) - f l z = 0) → ∀ b₀ ∈ B, ∃ U : Set E, IsOpen U ∧ b₀ ∈ U ∧ U ⊆ B ∧ IsPreconnected U ∧ ∃ s : Fl g → E → ℂ, (∀ l ∈ stdLat g, ContinuousOn (s l) U) ∧ (∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, ∀ b ∈ U, s (l + l') b = s l b + s l' b) ∧ ∃ φ : Pt E g → ℂ, IsBundleIso U τ (stdLat g) (fun l P => Complex.exp (2 * π * Complex.I * s l P.1)) u φ := by
  first | exact @GlobalTheory.FactorDegreeZero.factor_degree_zero_normal_form | exact GlobalTheory.FactorDegreeZero.factor_degree_zero_normal_form | (intros; apply GlobalTheory.FactorDegreeZero.factor_degree_zero_normal_form <;> assumption)
