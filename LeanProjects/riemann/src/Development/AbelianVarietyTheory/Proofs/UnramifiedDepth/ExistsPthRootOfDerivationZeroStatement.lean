import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsPthRootOfDerivationZero
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pth_root_of_derivation_zero : ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (f : K), (∀ D : Derivation ℤ K K, D f = 0) → ∃ h : K, h ^ p = f := by
  first | exact @GlobalTheory.exists_pow_eq_of_forall_derivation_eq_zero | exact GlobalTheory.exists_pow_eq_of_forall_derivation_eq_zero | (intros; apply GlobalTheory.exists_pow_eq_of_forall_derivation_eq_zero <;> assumption)
