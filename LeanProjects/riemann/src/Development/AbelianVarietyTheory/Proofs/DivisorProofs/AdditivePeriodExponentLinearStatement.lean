import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditivePeriodExponentLinear
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additive_period_exponent_linear : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {U : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap U τ → IsPreconnected U → ∀ (s : Fl g → E → ℂ) (a : E → Fin g → ℂ), (∀ l ∈ stdLat g, ContinuousOn (s l) U) → (∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, ∀ b ∈ U, s (l + l') b = s l b + s l' b) → DifferentiableOn ℂ a U → (∀ l ∈ stdLat g, ∀ b ∈ U, Complex.exp (a b ⬝ᵥ per (τ b) l) = Complex.exp (4 * π * Complex.I * s l b)) → ∃ x : Fl g, IsBundleIso U τ (stdLat g) (fun l _ => Complex.exp (2 * π * Complex.I * (-(riem x l : ℂ)))) (fun l P => Complex.exp (2 * π * Complex.I * s l P.1)) (fun P => Complex.exp (a P.1 ⬝ᵥ P.2 / 2)) := by
  first | exact @GlobalTheory.HalfPeriodChar.flat_of_exp_eq | exact GlobalTheory.HalfPeriodChar.flat_of_exp_eq | (intros; apply GlobalTheory.HalfPeriodChar.flat_of_exp_eq <;> assumption)
