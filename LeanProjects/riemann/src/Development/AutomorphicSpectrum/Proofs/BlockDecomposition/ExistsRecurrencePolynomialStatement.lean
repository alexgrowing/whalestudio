import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRecurrencePolynomial
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.CommonEigenvectors.KillPoly
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_recurrence_polynomial : ∀ (G : Type) [Group G] (a : ℝ → G) (F₀ : G → ℂ) (S : Submodule ℂ (ℝ → ℂ)), (∀ s t, a (s + t) = a s * a t) →
  (∀ g, Continuous fun t => F₀ (a t * g)) → FiniteDimensional ℂ S → (∀ g, (fun t => F₀ (a t * g)) ∈ S) →
  ∃ p : ℂ[X], p.Monic ∧ p.natDegree ≤ Module.finrank ℂ S ∧ (∀ g, ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * F₀ (a j * g) = 0) ∧
    ∀ z, p.IsRoot z → ∃ c : ℂ, z = Complex.exp c ∧
      ∃ F ∈ Submodule.span ℂ (Set.range fun t : ℝ => fun g => F₀ (a t * g)), F ≠ 0 ∧
        ∀ (t : ℝ) g, F (a t * g) = Complex.exp (c * t) * F g := by
  first | exact @GlobalTheory.CompanionTheory.KillDeg.killPoly_natDegree_le | exact GlobalTheory.CompanionTheory.KillDeg.killPoly_natDegree_le | (intros; apply GlobalTheory.CompanionTheory.KillDeg.killPoly_natDegree_le <;> assumption)
