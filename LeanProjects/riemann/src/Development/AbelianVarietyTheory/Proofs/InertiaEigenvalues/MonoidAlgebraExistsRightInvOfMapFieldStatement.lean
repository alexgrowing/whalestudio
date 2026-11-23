import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonoidAlgebraExistsRightInvOfMapField
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monoidAlgebra_exists_right_inv_of_map_field : ∀ {E L G : Type} [Field E] [Field L] [Group G] [Fintype G] (j : E →+* L) (x : MonoidAlgebra E G), (∃ v : MonoidAlgebra L G, MonoidAlgebra.mapRingHom G j x * v = 1) → ∃ v : MonoidAlgebra E G, x * v = 1 := by
  first | exact @GlobalTheory.groupAlgebra_exists_right_inv_of_map | exact GlobalTheory.groupAlgebra_exists_right_inv_of_map | (intros; apply GlobalTheory.groupAlgebra_exists_right_inv_of_map <;> assumption)
