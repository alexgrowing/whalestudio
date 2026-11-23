import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GuDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsGalRepOfOfIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompC
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatLoc
open UpperTheory.V.Af UpperTheory.V.Af.Gu

theorem UpperTheory.satake_galois_compatibility_of_hecke_eigensystem :
    HypothesesH → SatLink := by
  intro PH E _ _ _ a π
  have P := PH.toClassicalTheorems
  refine ⟨fun w σ hσ B => (satLoc P E a w σ).2 _ π.finPart ((locCompC P E a π w).2 σ hσ) B, ?_⟩
  exact ExLib.eventually_sat (satLoc P) π.finPart π.isSmooth_finPart fun w =>
    let ⟨⟨σ, hσ⟩, hi⟩ := locCompC P E a π w
    ⟨σ, hi σ hσ⟩
