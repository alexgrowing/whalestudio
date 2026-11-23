import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHostCongruencePrimes
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DuStarPos
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SpreadLe
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
import Formalism.SharpRestriction.InertJacobiLevels.HostFam
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_host_congruence_primes : ∀ (R : Ranks), Function.Injective R.h → R.o ^ 64 ≤ 2 ^ R.e → 2 ≤ R.e → ∀ (B N : ℕ) (TT : Finset (R.A)), ∃ H : Host R, H.splitBound = B ∧ N < H.q ∧ N < H.d ∧ H.ccK = ⊤ ∧ H.TT = TT ∧ (∀ k, H.g k % (H.QS * H.q * H.d) = 1) ∧ Disjoint (Formalism.CyclotomicNorms.BB R.r (H.g 0)) (Formalism.CyclotomicNorms.BB R.r (H.g 1)) ∧ (∀ p ∈ H.levelPrimes, p.Prime ∧ p % (H.QS * H.q * H.d) = 1) ∧ (∀ k, N < H.g k) ∧ (∀ k, ∃ π : 𝓞 H.E, (π : H.E) ∈ H.K ∧ (π : H.E) * H.conj (π : H.E) = (H.g k : H.E) ∧ ((H.QS * H.q * H.d : ℕ) : 𝓞 H.E) ∣ π - 1) ∧ H.pde % (H.QS * H.q * H.d) = 1 ∧ H.pde' % (H.QS * H.q * H.d) = 1 := by
  first | exact @GlobalTheory.Mem.exists_host_level_primes_one_mod | exact GlobalTheory.Mem.exists_host_level_primes_one_mod | (intros; apply GlobalTheory.Mem.exists_host_level_primes_one_mod <;> assumption)
