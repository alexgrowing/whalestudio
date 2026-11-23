import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsTransfer
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsShaHalf
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsHyp

noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.Lit1.PTN

theorem ptfsHyp_of_cmp (hN : NineCmpFS) (hS : ShaCmpFS) : PositivityTheory.PTN.PtfsHyp := by
  intro K _ _ l _ r hl hr ζ hζ inv hinv S hS' Av hAv μ hμ M _ _ _ _ _ ρ hρ
  exact ⟨nineTermExact_of_nineCmp S Av μ _ ρ hρ
      (hN K l r hl hr ζ hζ inv hinv S hS' Av hAv μ hμ M ρ hρ),
    shaDual_of_perfectPair S Av μ ρ (hS K l r hl hr ζ hζ inv hinv S hS' Av hAv μ hμ M ρ hρ).1
      (hS K l r hl hr ζ hζ inv hinv S hS' Av hAv μ hμ M ρ hρ).2⟩

end PositivityTheory.Lit1.PTN
