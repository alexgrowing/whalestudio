import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictRing
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantTopologyComparison.FiniteNeighbourhoodSecond

noncomputable section

open IsDedekindDomain NumberField

namespace PI.VolStabW

def SAf : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (U : AddSubgroup (FiniteAdeleRing (𝓞 F) F)),
    IsOpen (U : Set (FiniteAdeleRing (𝓞 F) F)) →
    ∀ x : FiniteAdeleRing (𝓞 F) F, ∃ a : F, x - algebraMap F (FiniteAdeleRing (𝓞 F) F) a ∈ U

theorem sAf_holds : SAf := by
  intro F _ _ U hU x
  obtain ⟨m, hm, hmx⟩ := PIW.AdelClassFin.DictRing.af_denom x
  obtain ⟨N, hN1, hNU⟩ := PI.InvTopW.finite_neighbourhood_second F U (hU.mem_nhds U.zero_mem)
  obtain ⟨β, y, hy, hxy⟩ := PIW.AdelClassFin.DictRing.af_approx _ hmx (m * N)
    (Nat.mul_pos hm (by omega))
  refine ⟨(β : F) / (m : F), ?_⟩
  have hmF : (m : F) ≠ 0 := by exact_mod_cast hm.ne'
  have hu : IsUnit (algebraMap F (FiniteAdeleRing (𝓞 F) F) (m : F)) :=
    (IsUnit.mk0 _ hmF).map _
  have key : x - algebraMap F (FiniteAdeleRing (𝓞 F) F) ((β : F) / (m : F)) =
      (N : FiniteAdeleRing (𝓞 F) F) * y := by
    apply hu.mul_left_cancel
    have e1 : algebraMap F (FiniteAdeleRing (𝓞 F) F) (m : F) = (m : FiniteAdeleRing (𝓞 F) F) :=
      map_natCast _ m
    have e2 : algebraMap F (FiniteAdeleRing (𝓞 F) F) (m : F) *
        algebraMap F (FiniteAdeleRing (𝓞 F) F) ((β : F) / (m : F)) =
        algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) β := by
      rw [← map_mul, mul_div_cancel₀ _ hmF, IsScalarTower.algebraMap_apply (𝓞 F) F]
    rw [mul_sub, e2, e1]
    rw [hxy]
    push_cast
    ring
  rw [key]
  exact hNU y hy

end PI.VolStabW
