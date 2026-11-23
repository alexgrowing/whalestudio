import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GlobalEulerCharAtOfRatioOne
import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.Assemble
import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.LemmaX

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace PositivityTheory.Lit1.GEN

theorem globalEulerChar_of_lemmaX (hX : GlobalEulerCharCoprime) : ReciprocityTheory.Gal.GlobalEulerChar := by
  intro F Ω _ _ _ _ _ l _ r M _ _ _ _ _ S rhoS
  exact globalEulerCharAt_of_ratioOne S rhoS (ratioOne_of_lemmaX l hX)

theorem globalEulerChar_full : ReciprocityTheory.Gal.GlobalEulerChar :=
  globalEulerChar_of_lemmaX X.lemmaX

end PositivityTheory.Lit1.GEN
