import Mathlib
import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbolBridge
import GroundTheory.ProfiniteCohomology.LocalClassFormationAlt
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

section Transfer

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep A]

noncomputable def PreClassFormation.toInt (F : PreClassFormation A) :
    PreClassFormation (uliftIntToIntRep A) where
  inv U := (F.inv U).comp
    (cohomologyULiftIntAddEquiv (Rep.res (U : Subgroup G).subtype A) 2).symm.toAddMonoidHom
  isZero_H1_open_subgroups U := by
    have : Subsingleton (cohomology (Rep.res (U : Subgroup G).subtype A) 1) :=
      ModuleCat.isZero_iff_subsingleton.1 (F.isZero_H1_open_subgroups U)
    have : Subsingleton (cohomology (uliftIntToIntRep (Rep.res (U : Subgroup G).subtype A)) 1) :=
      (cohomologyULiftIntAddEquiv (Rep.res (U : Subgroup G).subtype A) 1).symm.subsingleton
    exact ModuleCat.isZero_of_subsingleton _
  inv_res U V h x := by
    obtain ⟨y, rfl⟩ := (cohomologyULiftIntAddEquiv (Rep.res (U : Subgroup G).subtype A) 2).surjective x
    have e := cohomologyULiftIntAddEquiv_cohomologyMapAlong (Rep.res (U : Subgroup G).subtype A)
      (Subgroup.inclusion (show (V : Subgroup G) ≤ U from h)) (continuous_subgroup_inclusion _)
      (resResHom A (show (V : Subgroup G) ≤ U from h))
      (resResHom (uliftIntToIntRep A) (show (V : Subgroup G) ≤ U from h)) (fun _ => rfl) 2 y
    simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.symm_apply_apply]
    rw [cohomologyResLE_eq, ← e, AddEquiv.symm_apply_apply, ← cohomologyResLE_eq]
    exact F.inv_res U V h y

noncomputable def ClassFormation.toInt (F : ClassFormation A) : ClassFormation (uliftIntToIntRep A) where
  toPreClassFormation := PreClassFormation.toInt A F.toPreClassFormation
  inv_bijective U := (F.inv_bijective U).comp
    (cohomologyULiftIntAddEquiv (Rep.res (U : Subgroup G).subtype A) 2).symm.bijective

end Transfer

section Local

variable (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω]

noncomputable def brauerInvZ : cohomology (galUnitsZ K Ω) 2 →+ QZ :=
  (brauerInv K Ω).comp (cohomologyULiftIntAddEquiv (galUnits.{0} K Ω) 2).symm.toAddMonoidHom

theorem brauerInvZ_cohomologyULiftIntAddEquiv (x : galoisBrauerGroup K Ω) :
    brauerInvZ K Ω (cohomologyULiftIntAddEquiv (galUnits.{0} K Ω) 2 x) = brauerInv K Ω x :=
  congrArg (brauerInv K Ω) ((cohomologyULiftIntAddEquiv (galUnits.{0} K Ω) 2).symm_apply_apply x)

theorem brauerInvZ_bijective : Function.Bijective (brauerInvZ K Ω) :=
  (brauerInv_bijective K Ω).comp (cohomologyULiftIntAddEquiv (galUnits.{0} K Ω) 2).symm.bijective

noncomputable def localClassFormationZ : ClassFormation (galUnitsZ K Ω) :=
  ClassFormation.toInt (galUnits.{0} K Ω) (localClassFormation K Ω)

theorem localClassFormationZ_inv (U : OpenSubgroup Gal(Ω/K)) (x : H2Open (galUnitsZ K Ω) U) :
    (localClassFormationZ K Ω).inv U x = localInv K Ω U
      ((cohomologyULiftIntAddEquiv (Rep.res (U : Subgroup Gal(Ω/K)).subtype (galUnits.{0} K Ω)) 2).symm x) :=
  rfl

end Local

end GroundTheory.ProfCoh
