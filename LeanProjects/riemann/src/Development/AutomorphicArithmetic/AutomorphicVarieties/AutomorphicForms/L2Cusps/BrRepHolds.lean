import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompactAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CmBridge

theorem UpperTheory.V.KernelIndexFullLattice.brRep_holds :
    UpperTheory.V.KernelIndexFullLattice.BrRep := by
  intro E _ _ _ a π₀
  refine ⟨UpperTheory.V.Cm.ofRep π₀, ?_⟩
  change (π₀.carrier.map (UpperTheory.V.Cm.ofCusp E a)).map _ = _
  rw [← Submodule.map_comp]
  rfl
