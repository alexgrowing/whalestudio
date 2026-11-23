import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HermitianBlockInvariantsIffIsometry
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianBlock_invariants_iff_isometry : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (lam : F), A.IsGen τ p → (∀ (a : A.K) (X : Hn r F E), IsUnit a → HasInv X (A.invK τ p lam a) → ∀ (x : A.K) (y : A.L), IsUnit y → a = x * A.NL y → ∃ j : A.L ≃ₗ[E] (Fin r → E), A.IsIsom x j ∧ (∀ z, j (algebraMap A.K A.L τ * z) = X.1.1 *ᵥ j z) ∧ j y = X.2.1) ∧ ∀ (x : A.K) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → ∃ Ax : selfAdjoint (Matrix (Fin r) (Fin r) E), (∀ z, j (algebraMap A.K A.L τ * z) = Ax.1 *ᵥ j z) ∧ ∀ y, HasInv ((Ax, j y, lam) : Hn r F E) (A.invK τ p lam (x * A.NL y)) := by
  first | exact @GlobalTheory.EtIsom.herm_iff_isom | exact GlobalTheory.EtIsom.herm_iff_isom | (intros; apply GlobalTheory.EtIsom.herm_iff_isom <;> assumption)
