import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CommuteCapOfCommuteEop

open NumberField GlobalTheory.CuspRep

namespace GlobalTheory.CuspRep

theorem Zalg_mul_lie : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (X : GlobalTheory.CuspRep.Lie E a)
    (z : Module.End ℂ (GlobalTheory.CuspRep.Sm E a)), z ∈ GlobalTheory.CuspRep.Zalg E a →
      z * GlobalTheory.CuspRep.lie E a X = GlobalTheory.CuspRep.lie E a X * z := by
  intro E _ _ _ a X z hz
  have h : GlobalTheory.CuspRep.Zalg E a ≤ Subalgebra.centralizer ℂ {GlobalTheory.CuspRep.lie E a X} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨τ, u, rfl⟩
    intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    exact (commute_cap_lie τ u X).eq.symm
  exact ((Subalgebra.mem_centralizer_iff ℂ).1 (h hz) _ rfl).symm

end GlobalTheory.CuspRep
