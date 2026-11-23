import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.Reduce
import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.WorkDevis
import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.WorkAssemble

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN

theorem ratioOne_of_killed_l (ℓ : ℕ) [Fact ℓ.Prime] (P : FiniteSubfield → Prop) (h : RatioOneKilled ℓ P) :
    RatioOne ℓ P :=
  W_devis.ratioOne_of_killed_l ℓ P h

theorem ratioOne_of_lemmaX (ℓ : ℕ) [Fact ℓ.Prime] (hX : GlobalEulerCharCoprime) : RatioOne ℓ (fun _ => True) :=
  ratioOne_of_killed_l ℓ _ (W_assemble.ratioOneKilled_of_lemmaX ℓ hX)

end PositivityTheory.Lit1.GEN
