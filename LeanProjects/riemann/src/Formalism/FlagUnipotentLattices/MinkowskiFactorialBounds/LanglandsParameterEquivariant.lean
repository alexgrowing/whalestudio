import Formalism.FlagUnipotentLattices.InterlaceBlocksW
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.InterlacingOfBlocksSecondCase

open Formalism.HermitianLatticeCounting.S8 TensorProduct Finset

set_option linter.all false

noncomputable section

namespace Formalism.HermitianLatticeCounting.P

theorem LL_tmul {V U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U] {n : ℕ}
    (ℓ : V →ₗ[ℂ] U) (a : Fin n) (v : V) (y : Fin n → ℂ) : LLmap ℓ a (v ⊗ₜ[ℂ] y) = y a • ℓ v := by
  simp [LLmap]

theorem coord_sum {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ξ : Fin n → V) (a : Fin n) :
    LLmap LinearMap.id a (∑ c, ξ c ⊗ₜ[ℂ] (Pi.single c (1 : ℂ) : Fin n → ℂ)) = ξ a := by
  simp only [map_sum, LL_tmul, LinearMap.id_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb; simp [Pi.single_apply, Ne.symm hb]
  · simp

end Formalism.HermitianLatticeCounting.P
