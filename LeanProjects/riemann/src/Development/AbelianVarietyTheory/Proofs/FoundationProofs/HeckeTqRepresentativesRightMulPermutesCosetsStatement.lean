import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTqRepresentativesRightMulPermutesCosets
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeTqRepresentatives_right_mul_permutes_cosets : ∀ (N l q : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → q.Prime → ¬ q ∣ N * l → ∀ σ : SL(2, ℤ), IsDiam N l (q : ZMod N) σ → ∀ γ : Lev N l, ∃ π : Equiv.Perm (Fin (q + 1)), ∀ i, ∃ γ' : Lev N l, tqFam q σ i * mat γ = mat γ' * tqFam q σ (π i) := by
  first | exact @GlobalTheory.TqPerm.tqFam_perm | exact GlobalTheory.TqPerm.tqFam_perm | (intros; apply GlobalTheory.TqPerm.tqFam_perm <;> assumption)
