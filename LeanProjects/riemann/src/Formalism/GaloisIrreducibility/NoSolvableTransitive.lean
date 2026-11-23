import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.OrbitSubSum
import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.RestrictRoots
import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.LemmaAOf
import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.IrredOf
import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.PermSubSumInv
import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.ResiduesLe
import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.FewLargeParts
import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.BlockBoundOfOrbits
import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.OneNonUnit
import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.PowerPCycle
import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.AltNotSolvable
import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.NoSolvableOf
import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.PrimitiveOfPCycle
import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.JordanPrime

namespace Formalism.GaloisIrreducibility

theorem lemmaA : LemmaA := lemmaAOf_statement orbit_subset_sum restrict_roots_to_subfield

theorem irred : Irred := irreducible_of_galois_conditions lemmaA
theorem permSubSumInv : PermSubSumInv := permutation_subset_sum_invariant

theorem residuesLe : ResiduesLe := residues_count_le
theorem bbAtMostThree : BBAtMostThree := block_bound_of_orbits few_large_cycle_parts
theorem cardGL : CardGL := by
  intro K _ _ _ N
  have hinj : Function.Injective
      (fun g : GL (Fin N) K => fun i j : Fin N => (g : Matrix (Fin N) (Fin N) K) i j) := by
    intro g h hgh
    apply Units.ext
    exact Matrix.ext fun i j => congrFun (congrFun hgh i) j
  refine le_trans (Fintype.card_le_of_injective _ hinj) (le_of_eq ?_)
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, ← pow_mul, sq]

theorem primitiveOfPCycle : PrimitiveOfPCycle := primitive_of_p_cycle
theorem jordanPrime : JordanPrime := jordan_prime_cycle_theorem

theorem noSolvableTransitive : NoSolvableTransitive :=
  no_solvable_subgroup_of power_of_p_cycle primitive_of_p_cycle jordan_prime_cycle_theorem alternating_group_not_solvable

end Formalism.GaloisIrreducibility
