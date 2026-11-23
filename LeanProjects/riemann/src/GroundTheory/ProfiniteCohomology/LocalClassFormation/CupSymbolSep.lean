import Mathlib
import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbol
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open IntermediateField GroundTheory.LocalField

section Sep

variable (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

noncomputable def brauerInvZOfIsSepClosure : cohomology (galUnitsZ K Ω) 2 →+ QZ :=
  letI := algebraicValuativeRel K Ω
  letI := algebraicTopology K Ω
  haveI := algebraicTopology_isValuativeTopology K Ω
  haveI := algebraicValuativeRel_valuativeExtension K Ω
  brauerInvZ K Ω

theorem brauerInvZOfIsSepClosure_bijective : Function.Bijective (brauerInvZOfIsSepClosure K Ω) :=
  letI := algebraicValuativeRel K Ω
  letI := algebraicTopology K Ω
  haveI := algebraicTopology_isValuativeTopology K Ω
  haveI := algebraicValuativeRel_valuativeExtension K Ω
  brauerInvZ_bijective K Ω

variable {K Ω}

theorem brauerInvZOfIsSepClosure_galCupClass (χ : Additive Gal(Ω/K) →ₜ+ QZ) (a : Kˣ) (g : Gal(Ω/K))
    (hg : ∀ (y : Ω) (hy : y ∈ maximalAbelianExtension K Ω),
      g y = (localArtinMap K Ω a ⟨y, hy⟩ : Ω)) :
    brauerInvZOfIsSepClosure K Ω (galCupClass K Ω χ a) = χ (Additive.ofMul g) :=
  letI := algebraicValuativeRel K Ω
  letI := algebraicTopology K Ω
  haveI := algebraicTopology_isValuativeTopology K Ω
  haveI := algebraicValuativeRel_valuativeExtension K Ω
  brauerInvZ_galCupClass χ a g hg

end Sep

end GroundTheory.ProfCoh
