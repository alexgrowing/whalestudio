import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KerLEqTraceDotProductOfIsIsom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kerL_eq_trace_dotProduct_of_isIsom : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → ∀ y' y : A.L, A.kerL ψ x y' y = ψ (Algebra.trace F E (star (j y') ⬝ᵥ j y)) := by
  first | exact @GlobalTheory.JR.Et.kerL_eq_of_isIsom | exact GlobalTheory.JR.Et.kerL_eq_of_isIsom | (intros; apply GlobalTheory.JR.Et.kerL_eq_of_isIsom <;> assumption)
