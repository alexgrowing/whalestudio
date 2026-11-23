import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerFinitelyGeneratedModOpen
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
open Matrix GlobalTheory.LKRes
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralizer_finitely_generated_mod_open : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K → ∀ (n r : ℕ), 0 < r →
    ∀ N : GL (Fin n) (GlobalTheory.LKRes.KQ p K r), N.val.charpoly.Separable →
    ∃ G : Finset (GL (Fin n) (GlobalTheory.LKRes.KQ p K r)), (∀ g ∈ G, g ∈ Subgroup.centralizer {N}) ∧
      Subgroup.centralizer {N} ≤ Subgroup.closure ((G : Set (GL (Fin n) (GlobalTheory.LKRes.KQ p K r))) ∪
        ((Subgroup.centralizer {N} ⊓ GlobalTheory.LKRes.Kres p K n r : Subgroup _) : Set (GL (Fin n) (GlobalTheory.LKRes.KQ p K r)))) := by
  first | (exact @GlobalTheory.CentFG.centralizer_le_closure) | (exact GlobalTheory.CentFG.centralizer_le_closure) | (intros; apply GlobalTheory.CentFG.centralizer_le_closure <;> assumption)
