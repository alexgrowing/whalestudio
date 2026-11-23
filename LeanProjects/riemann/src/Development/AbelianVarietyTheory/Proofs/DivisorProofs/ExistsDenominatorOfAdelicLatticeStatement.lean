import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDenominatorOfAdelicLattice
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_denominator_of_adelic_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ y : (Af E)ˣ,
    ∃ N : ℕ, 0 < N ∧ (∀ x : 𝓞 E, (N : E) * algebraMap (𝓞 E) E x ∈ lattice c y) ∧ ∀ x ∈ lattice c y, IsIntegral ℤ ((N : E) * x) := by
  first | exact @GlobalTheory.CMVal.LatBound.lattice_between | exact GlobalTheory.CMVal.LatBound.lattice_between | (intros; apply GlobalTheory.CMVal.LatBound.lattice_between <;> assumption)
