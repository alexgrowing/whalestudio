import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CommuteCapOfCommuteEop

noncomputable section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.ZalgCentral

theorem Zalg_mul_lie : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (z : Module.End ℂ (Sm E a)),
    z ∈ Zalg E a → ∀ X, z * lie E a X = lie E a X * z := by
  intro E _ _ _ a z hz X
  unfold Zalg at hz
  have hle : Algebra.adjoin ℂ {z : Module.End ℂ (Sm E a) | ∃ τ u, z = cap τ u} ≤
      Subalgebra.centralizer ℂ {lie E a X} := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨τ, u, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact (commute_cap_lie τ u X).symm.eq
  have hc := (Subalgebra.mem_centralizer_iff ℂ).mp (hle hz) (lie E a X) (Set.mem_singleton _)
  exact hc.symm

end GlobalTheory.CompanionTheory.ZalgCentral
