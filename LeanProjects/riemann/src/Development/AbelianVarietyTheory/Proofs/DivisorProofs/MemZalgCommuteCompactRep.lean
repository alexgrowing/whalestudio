import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL

open NumberField GlobalTheory.CuspRep

namespace GlobalTheory.ZalgCpt

theorem zalg_comm_cptRep : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (k : GlobalTheory.CuspRep.Kinf E a) (z : Module.End ℂ (GlobalTheory.CuspRep.Sm E a)),
    z ∈ GlobalTheory.CuspRep.Zalg E a → z * GlobalTheory.CuspRep.cptRep E a k = GlobalTheory.CuspRep.cptRep E a k * z := by
  intro E _ _ _ a k z hz
  have hle : GlobalTheory.CuspRep.Zalg E a ≤ Subalgebra.centralizer ℂ {GlobalTheory.CuspRep.cptRep E a k} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨τ, u, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    rintro g rfl
    exact (GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u (Unitary.toUnits k)).eq.symm
  exact ((Subalgebra.mem_centralizer_iff ℂ).1 (hle hz) _ rfl).symm

end GlobalTheory.ZalgCpt
