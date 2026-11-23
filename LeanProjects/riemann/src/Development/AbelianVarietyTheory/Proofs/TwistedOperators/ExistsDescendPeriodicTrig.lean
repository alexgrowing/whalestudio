import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DescMk

open MeasureTheory

namespace GlobalTheory

theorem trigPoly_dense_periodic : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x, ∃ γ ∈ Γ, γ + x ∈ K) → ∀ (A : Type) [AddCommGroup A] (χ : A → G → ℂ), (∀ a, Continuous (χ a)) → (∀ a x y, χ a (x + y) = χ a x * χ a y) → (∀ a b x, χ (a + b) x = χ a x * χ b x) → (∀ x, χ 0 x = 1) → (∀ a x, ‖χ a x‖ = 1) → (∀ x, (∀ a, χ a x = 1) ↔ x ∈ Γ) → ∀ Φ : G → ℂ, Continuous Φ → (∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x) → ∀ ε : ℝ, 0 < ε → ∃ (s : Finset A) (c : A → ℂ), ∀ x, ‖Φ x - ∑ a ∈ s, c a * χ a x‖ ≤ ε := by
  first
  | exact @_root_.GlobalTheory.QuotientDescentTwistedOperators.approx
  | exact _root_.GlobalTheory.QuotientDescentTwistedOperators.approx
  | (apply _root_.GlobalTheory.QuotientDescentTwistedOperators.approx <;> assumption)
  | (intros; apply _root_.GlobalTheory.QuotientDescentTwistedOperators.approx <;> assumption)
  | (intros; apply @_root_.GlobalTheory.QuotientDescentTwistedOperators.approx <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.QuotientDescentTwistedOperators.approx ..)

end GlobalTheory
