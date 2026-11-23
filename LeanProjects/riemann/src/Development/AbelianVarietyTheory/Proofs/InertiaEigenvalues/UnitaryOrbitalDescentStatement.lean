import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryOrbitalDescent
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_test_orbU_eq_orbL : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (m : A.Meas ψ) (r : ℕ) (M : Meas r F E) (τ : A.K) (p : Fin r → F) (lam : F), A.IsGen τ p → ∀ (x : A.Kˣ) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → ∀ Ax : selfAdjoint (Matrix (Fin r) (Fin r) E), (∀ z, j (algebraMap A.K A.L τ * z) = Ax.1 *ᵥ j z) → ∀ f : Hn r F E → ℂ, IsTest f → ∃ φ : A.L → ℂ, IsTest φ ∧ ∀ y : A.L, IsUnit y → orbU M f (Ax, j y, lam) = A.orbL m.ν φ y ∧ orbU M (fourU M ψ f) (Ax, j y, lam) = A.orbL m.ν (fourB (m.μL x) (A.kerL ψ x) φ) y := by
  first | exact @GlobalTheory.JR.unitary_orbital_descent | exact GlobalTheory.JR.unitary_orbital_descent | (intros; apply GlobalTheory.JR.unitary_orbital_descent <;> assumption)
