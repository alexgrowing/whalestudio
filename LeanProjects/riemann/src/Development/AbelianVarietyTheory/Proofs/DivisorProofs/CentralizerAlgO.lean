import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MemUQptsStarCIff

noncomputable section
open scoped TensorProduct
namespace GlobalTheory.UPel.HT
variable {p : ℕ} [Fact p.Prime] (D : Datum p)

def Datum.algO : Subalgebra ℚ (Module.End ℚ D.VQ) := Algebra.adjoin ℚ (Set.range D.actQ)

theorem Datum.actQ_mem_algO (b : D.O) : D.actQ b ∈ D.algO := Algebra.subset_adjoin ⟨b, rfl⟩

theorem Datum.centralizer_algO : Subalgebra.centralizer ℚ (D.algO : Set (Module.End ℚ D.VQ)) = D.endO := by
  apply le_antisymm
  · exact Subalgebra.centralizer_le ℚ _ _ (Algebra.subset_adjoin)
  · intro g hg
    rw [Subalgebra.mem_centralizer_iff]
    intro h hh
    have hle : D.algO ≤ Subalgebra.centralizer ℚ ({g} : Set (Module.End ℚ D.VQ)) := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨b, rfl⟩
      rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
      rintro _ rfl
      exact (D.mem_endO.1 hg b).symm
    exact ((Subalgebra.mem_centralizer_iff ℚ).1 (hle hh) g rfl).symm

instance Datum.nontrivialVQ : Nontrivial D.VQ := by
  apply Module.nontrivial_of_finrank_pos (R := ℚ)
  haveI := D.freeLa; haveI := D.finLa
  rw [Module.finrank_baseChange, D.rankLa]
  exact Nat.mul_pos (Nat.mul_pos D.m_pos D.n_pos) Module.finrank_pos

end GlobalTheory.UPel.HT
