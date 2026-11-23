import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsUnitIffCharpolyCoeffZeroNe
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteMonicNatDegree
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.EqZeroOfNotPrimaryStatement

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem ipGL_rootSum_eq_sum_torus : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (θ : AlgebraicClosure F →* ℂ) (φ : Module.End F V → ℂ), IsClassFn φ → IsPrimitive φ → 0 < Module.finrank F V → ∀ l : ℕ, ipGL φ (fun g : Module.End F V => rootSum θ l (LinearMap.charpoly g)) = ∑ᶠ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ Module.finrank F V - 1) = 1}, ((Module.finrank F V / (minpoly F α).natDegree : ℕ) : ℂ) * mass φ (minpoly F α ^ (Module.finrank F V / (minpoly F α).natDegree)) * star (θ α ^ l) := by
  intro F _ _ V _ _ _ θ φ hcl hprim hpos l
  rw [ipGL_charpoly_eq_finsum_mass F V φ (rootSum θ l)]
  refine sum_poly_eq_sum_torus F θ (Module.finrank F V) hpos (mass φ) l ?_

  intro P _ _ hP
  unfold mass
  rw [finsum_mem_def]
  refine finsum_eq_zero_of_forall_eq_zero fun g => ?_
  by_cases hg : LinearMap.charpoly g = P
  · rw [Set.indicator_of_mem (show g ∈ {g : Module.End F V | LinearMap.charpoly g = P} from hg)]
    exact GlobalTheory.T.classFn_eq_zero_of_charpoly_not_irreducible_pow F V φ hcl hprim hpos g (hg ▸ hP)
  · exact Set.indicator_of_notMem (show g ∉ {g : Module.End F V | LinearMap.charpoly g = P} from hg) _

end GlobalTheory.CuspGL
