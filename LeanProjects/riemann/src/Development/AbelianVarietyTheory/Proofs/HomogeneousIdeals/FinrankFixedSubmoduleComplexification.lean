import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsRingEquivOfIsTranscendenceBasis
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueHomogeneousIdealFixedSubalgebra
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueComapEqVanishingIdeal

open TensorProduct CategoryTheory AlgebraicGeometry

universe u

namespace GlobalTheory.GaloisDescent

section Instances

variable (K L G V : Type*) [CommSemiring K] [Semiring L] [Algebra K L] [Monoid G]
  [MulSemiringAction G L]

end Instances

section Group

variable {K L G : Type*} [Field K] [Field L] [Algebra K L] [Group G] [MulSemiringAction G L]

end Group

section AlgEquiv

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

variable [Algebra K ℂ]

theorem complex_stable_iff_exists_baseChange {V : Type*} [AddCommGroup V]
    [Module K V] (W : Submodule ℂ (ℂ ⊗[K] V)) :
    (∀ σ : ℂ ≃ₐ[K] ℂ, ∀ w ∈ W, σ.toLinearMap.rTensor V w ∈ W) ↔
      ∃! N : Submodule K V, N.baseChange ℂ = W :=
  stable_iff_exists_baseChange (fun σ : ℂ ≃ₐ[K] ℂ => σ.toAlgHom)
    complex_mem_range_of_forall_algEquiv W

end AlgEquiv

end GlobalTheory.GaloisDescent
