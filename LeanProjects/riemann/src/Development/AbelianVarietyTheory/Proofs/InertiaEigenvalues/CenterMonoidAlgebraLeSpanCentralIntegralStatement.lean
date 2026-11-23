import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CenterMonoidAlgebraLeSpanCentralIntegral
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.center_monoidAlgebra_le_span_centralIntegral : ∀ (R G : Type) [CommRing R] [Group G] [Finite G] (z : MonoidAlgebra R G), z ∈ Subalgebra.center R (MonoidAlgebra R G) → z ∈ Submodule.span R ((MonoidAlgebra.mapRingHom G (Int.castRingHom R)) '' {c : MonoidAlgebra ℤ G | ∀ a, c * a = a * c}) := by
  first | exact @GlobalTheory.GroupAlg.center_mem_span_classSums | exact GlobalTheory.GroupAlg.center_mem_span_classSums | (intros; apply GlobalTheory.GroupAlg.center_mem_span_classSums <;> assumption)
