import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsFieldAndPthRootsOfLocalAlgFrobeniusFixed
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isField_and_pthRoots_of_localAlg_frobenius_fixed : ∀ (p : ℕ) [Fact p.Prime] (k A : Type) [Field k] [CharP k p] [CommRing A] [Algebra k A] [IsLocalRing A]
  (T : Finset A) (f : ℕ), 0 < f → Algebra.adjoin k (T : Set A) = ⊤ → (∀ t ∈ T, t ^ p ^ f = t) →
  IsField A ∧ ∀ (y : A) (a : k), y ^ p = algebraMap k A a → ∃ b : k, y = algebraMap k A b := by
  first | exact @GlobalTheory.localAlg_frob_fixed_isField_and_pth_roots | exact GlobalTheory.localAlg_frob_fixed_isField_and_pth_roots | (intros; apply GlobalTheory.localAlg_frob_fixed_isField_and_pth_roots <;> assumption)
