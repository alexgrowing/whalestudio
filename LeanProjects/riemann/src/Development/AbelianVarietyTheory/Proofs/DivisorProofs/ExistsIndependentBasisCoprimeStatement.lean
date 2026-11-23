import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIndependentBasisCoprime
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_independent_basis_coprime : ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] [Module.Finite ℤ M] [IsAddTorsionFree M] (N : ℕ), 2 ≤ N → ∃ (r : ℕ) (x : Fin r → M), LinearIndependent (𝓞 F) x ∧ ∃ c : 𝓞 F, c ≠ 0 ∧ IsCoprime c (N : 𝓞 F) ∧ ∀ m : M, c • m ∈ Submodule.span (𝓞 F) (Set.range x) := by
  first | exact @GlobalTheory.CoprimeBasis.exists_coprime_basis | exact GlobalTheory.CoprimeBasis.exists_coprime_basis | (intros; apply GlobalTheory.CoprimeBasis.exists_coprime_basis <;> assumption)
