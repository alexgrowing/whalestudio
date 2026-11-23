import Mathlib
import GroundTheory.GlobalFields.HerbrandQuotients.Cyclic
import GroundTheory.GlobalFields.HerbrandQuotients.Lattice
import GroundTheory.GlobalFields.HerbrandQuotients.Permutation
import GroundTheory.GlobalFields.HerbrandQuotients.CycTate

namespace GroundTheory.Global

open MulAction
open scoped TensorProduct

variable {G : Type*} [Group G] [Fintype G]

theorem cyclicHerbrand_eq_cycHerbrand {M : Type*} [AddCommGroup M] (ρ : Representation ℤ G M)
    (σ : G) : cyclicHerbrand ρ σ = cycHerbrand ρ σ :=
  rfl

theorem cycHerbrand_trivial_int (σ : G) :
    cycHerbrand (Representation.trivial ℤ G ℤ) σ = Fintype.card G :=
  cyclicHerbrand_trivial_int σ

theorem cycHerbrand_eq_of_real_equiv {M M' : Type*} [AddCommGroup M] [Module.Finite ℤ M]
    [Module.Free ℤ M] [AddCommGroup M'] [Module.Finite ℤ M'] [Module.Free ℤ M']
    (ρ : Representation ℤ G M) (ρ' : Representation ℤ G M') (σ : G)
    (e : ℝ ⊗[ℤ] M ≃ₗ[ℝ] ℝ ⊗[ℤ] M')
    (he : ∀ g x, e ((ρ g).baseChange ℝ x) = (ρ' g).baseChange ℝ (e x)) :
    cycHerbrand ρ σ = cycHerbrand ρ' σ :=
  cyclicHerbrand_eq_of_real_equiv ρ ρ' σ e he

end GroundTheory.Global
