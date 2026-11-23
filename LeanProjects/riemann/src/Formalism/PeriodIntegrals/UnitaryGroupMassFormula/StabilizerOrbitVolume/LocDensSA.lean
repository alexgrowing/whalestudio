import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictRing
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantTopologyComparison.FiniteNeighbourhoodSecond

noncomputable section

open IsDedekindDomain NumberField

namespace PI.VolStabSW

def SAf : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (U : AddSubgroup (FiniteAdeleRing (𝓞 F) F)),
    IsOpen (U : Set (FiniteAdeleRing (𝓞 F) F)) →
    ∀ x : FiniteAdeleRing (𝓞 F) F, ∃ a : F, x - algebraMap F (FiniteAdeleRing (𝓞 F) F) a ∈ U

theorem sAf_holds : SAf := by
  intro F _ _ U hU x
  obtain ⟨N, hN, hNU⟩ := PI.InvTopW.finite_neighbourhood_second F (U : Set (FiniteAdeleRing (𝓞 F) F)) (hU.mem_nhds U.zero_mem)
  obtain ⟨m, hm, hmx⟩ := PIW.AdelClassFin.DictRing.af_denom (F := F) x
  obtain ⟨β, y, hy, e⟩ := PIW.AdelClassFin.DictRing.af_approx (F := F) _ hmx (m * N) (Nat.mul_pos hm (by omega))
  refine ⟨(β : F) / m, ?_⟩
  have hm0 : (m : F) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hu : (m : FiniteAdeleRing (𝓞 F) F) * algebraMap F (FiniteAdeleRing (𝓞 F) F) ((m : F)⁻¹) = 1 := by
    rw [← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)) m, ← map_mul, mul_inv_cancel₀ hm0, map_one]
  have hβ : algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) β = algebraMap F (FiniteAdeleRing (𝓞 F) F) (β : F) :=
    IsScalarTower.algebraMap_apply (𝓞 F) F _ β
  have hdiv : algebraMap F (FiniteAdeleRing (𝓞 F) F) ((β : F) / m) =
      algebraMap F (FiniteAdeleRing (𝓞 F) F) (β : F) * algebraMap F (FiniteAdeleRing (𝓞 F) F) ((m : F)⁻¹) := by
    rw [div_eq_mul_inv, map_mul]
  have key : x - algebraMap F (FiniteAdeleRing (𝓞 F) F) ((β : F) / m) = (N : FiniteAdeleRing (𝓞 F) F) * y := by
    rw [hdiv, ← hβ]
    push_cast at e
    linear_combination algebraMap F (FiniteAdeleRing (𝓞 F) F) ((m : F)⁻¹) * e -
      (x - (N : FiniteAdeleRing (𝓞 F) F) * y) * hu
  rw [key]
  exact hNU y hy

end PI.VolStabSW
