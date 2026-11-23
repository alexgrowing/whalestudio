import Mathlib
import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbolSep
import GroundTheory.ProfiniteCohomology.LocalClassFormation.InvariantRes
import GroundTheory.LocalFields.LocalArtinBaseChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory IntermediateField GroundTheory.LocalField

noncomputable section

variable (Kv Ω : Type) [Field Kv] [ValuativeRel Kv] [TopologicalSpace Kv] [IsNonarchimedeanLocalField Kv]
  [Field Ω] [Algebra Kv Ω] [IsSepClosure Kv Ω] (L : IntermediateField Kv Ω)

def galUnitsZResScalars :
    Rep.res (AlgEquiv.restrictScalarsHom Kv : Gal(Ω/L) →* Gal(Ω/Kv)) (galUnitsZ Kv Ω) ⟶ galUnitsZ L Ω :=
  Rep.ofHom ⟨LinearMap.id, fun _ => LinearMap.ext fun _ => rfl⟩

def brauerResZ : cohomology (galUnitsZ Kv Ω) 2 ⟶ cohomology (galUnitsZ L Ω) 2 :=
  cohomologyMapAlong (AlgEquiv.restrictScalarsHom Kv) (continuous_restrictScalarsHom_of_tower Kv L Ω)
    (galUnitsZResScalars Kv Ω L) 2

theorem brauerResZ_eq_zero_of_finrank_smul [FiniteDimensional Kv L] (y : cohomology (galUnitsZ Kv Ω) 2)
    (hy : Module.finrank Kv L • brauerInvZOfIsSepClosure Kv Ω y = 0) : (brauerResZ Kv Ω L).hom y = 0 := by
  let := algebraicValuativeRel Kv Ω
  let := algebraicTopology Kv Ω
  have := algebraicTopology_isValuativeTopology Kv Ω
  have := algebraicValuativeRel_valuativeExtension Kv Ω
  obtain ⟨x, rfl⟩ := (cohomologyULiftIntAddEquiv (galUnits.{0} Kv Ω) 2).surjective y
  have e := cohomologyULiftIntAddEquiv_cohomologyMapAlong (galUnits.{0} Kv Ω)
    (AlgEquiv.restrictScalarsHom Kv) (continuous_restrictScalarsHom_of_tower Kv L Ω)
    (galUnitsResScalars Kv L Ω) (galUnitsZResScalars Kv Ω L) (fun _ => rfl) 2 x
  have h0 : brauerInvZOfIsSepClosure Kv Ω (cohomologyULiftIntAddEquiv (galUnits.{0} Kv Ω) 2 x) =
      brauerInv Kv Ω x :=
    brauerInvZ_cohomologyULiftIntAddEquiv Kv Ω x
  have h1 : brauerInv L Ω ((brauerRes Kv L Ω).hom x) = 0 := by
    rw [brauerInv_brauerRes, ← h0]
    exact hy
  have h2 : (brauerRes Kv L Ω).hom x = 0 :=
    (brauerInv_bijective L Ω).1 (h1.trans (map_zero _).symm)
  have h3 : cohomologyULiftIntAddEquiv (galUnits.{0} L Ω) 2 ((brauerRes Kv L Ω).hom x) = 0 := by
    rw [h2, map_zero]
  rw [brauerRes_eq] at h3
  exact e.symm.trans h3

end

end GroundTheory.ProfCoh
