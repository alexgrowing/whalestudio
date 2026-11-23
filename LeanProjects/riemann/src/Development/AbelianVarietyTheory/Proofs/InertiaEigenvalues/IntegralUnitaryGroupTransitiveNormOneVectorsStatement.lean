import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralUnitaryGroupTransitiveNormOneVectors
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralUnitaryGroup_transitive_norm_one_vectors : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (v : Fin (r + 1) → E), (∀ i, ‖v i‖ ≤ 1) → star v ⬝ᵥ v = 1 → ∃ k ∈ uO (r + 1) E, k.1 *ᵥ Pi.single (Fin.last r) 1 = v := by
  first | exact @GlobalTheory.UnitaryTransitive.uO_transitive | exact GlobalTheory.UnitaryTransitive.uO_transitive | (intros; apply GlobalTheory.UnitaryTransitive.uO_transitive <;> assumption)
