import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankAddLeFinrankRangeAddOfComapLe
import Mathlib
open TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_add_finrank_le_finrank_range_add_finrank : ∀ (k : Type) [Field k] (E A M : Type) [AddCommGroup E] [Module k E] [AddCommGroup A] [Module k A] [AddCommGroup M] [Module k M] (π : E →ₗ[k] A) (ν : E →ₗ[k] M) (Z : Submodule k A) (R U : Submodule k M) [FiniteDimensional k ↥(LinearMap.range π)] [FiniteDimensional k ↥U], Z ≤ LinearMap.range π → R ≤ U → U ≤ LinearMap.range ν → (∀ e, π e ∈ Z → ν e ∈ R) → finrank k ↥Z + finrank k ↥U ≤ finrank k ↥(LinearMap.range π) + finrank k ↥R := by
  first | exact @GlobalTheory.finrank_add_le_finrank_range_add_of_comap_le | exact GlobalTheory.finrank_add_le_finrank_range_add_of_comap_le | (intros; apply GlobalTheory.finrank_add_le_finrank_range_add_of_comap_le <;> assumption)
