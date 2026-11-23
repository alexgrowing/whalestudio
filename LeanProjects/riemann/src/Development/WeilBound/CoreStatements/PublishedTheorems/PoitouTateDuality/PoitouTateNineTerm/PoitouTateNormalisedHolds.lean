import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PoitouTateNineTerm.NineAddCore
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PoitouTateNormalisedOfNine

noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global ReciprocityTheory.Gal Formalism.ConjugateSelfDual
  GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

theorem nineAddFS_V : NineAddFS := by
  intro K _ _ l _ r hl hr ζ hζ inv hinv S hS Av hAv μ hμ M _ _ _ _ _ ρ hρ
  exact (foundData_nonempty ⟨K, inferInstance⟩ S hr ζ hζ hS Av hAv μ hμ ρ hρ).elim fun d =>
    nineAdd_core ⟨K, inferInstance⟩ hl hr ζ hζ inv hinv S hS Av hAv μ hμ M ρ hρ d

theorem poitouTateNormalised_holds : GlobalTheory.Published.PoitouTateNormalised :=
  PositivityTheory.PTN.poitouTateNormalised_of_nine (nineCmpFS_of_nineAddFS nineAddFS_V)

end PositivityTheory.Lit1.PTN
