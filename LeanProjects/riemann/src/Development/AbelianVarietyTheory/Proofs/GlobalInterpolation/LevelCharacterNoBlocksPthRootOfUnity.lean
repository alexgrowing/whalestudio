import Mathlib
import Formalism.LocalToGlobal.HermitianForms.TiedSym
import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GSplit
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ComplexRootOfUnityMemRangeOfIsPrimitiveRoot
open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace GlobalTheory

theorem lamJ_zero_blocks_mem_range_and_pow_eq_one :
    ∀ (k K : Type) [Field k] [Field K] (s : K →+* ℂ) (p : ℕ), p.Prime → (p : k) = 0 → (∃ ζ : K, IsPrimitiveRoot ζ p) → ∀ (n : ℕ) (ψ : AddChar k ℂ) (χ : ℕ → MulChar k ℂ) (a t skip : ℕ) (M : Matrix (Fin n) (Fin n) k), (∃ r : K, s r = lamJ ψ χ a t 0 skip M) ∧ lamJ ψ χ a t 0 skip M ^ p = 1 := by
  intro k K _ _ s p hp hk ⟨ζ, hζ⟩ n ψ χ a t skip M
  have hψ : ∀ x : k, ψ x ^ p = 1 := fun x => by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, hk, zero_mul, AddChar.map_zero_eq_one]
  have h : lamJ ψ χ a t 0 skip M ^ p = 1 := by
    unfold Formalism.L2.Forms.lamJ
    simp [hψ]
  exact ⟨complex_rootOfUnity_mem_range_of_isPrimitiveRoot K s p ζ hp.pos hζ _ h, h⟩

end GlobalTheory
