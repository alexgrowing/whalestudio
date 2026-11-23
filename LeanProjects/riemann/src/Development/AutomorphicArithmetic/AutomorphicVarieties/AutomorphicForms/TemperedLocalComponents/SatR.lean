import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompR
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SatOfFixed

theorem UpperTheory.V.Af.satR :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Af.SatR := by
  intro P F _ _ _ n M π hπ w hw
  obtain ⟨⟨σ, hσ⟩, h⟩ := locCompR P F n π w
  exact sat_of_isotypic (satLoc P) π.finPart hπ w hw σ (h σ hσ)
