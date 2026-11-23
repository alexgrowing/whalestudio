import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalFiniteness.FiniteH2TorsionModule
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteH1UnramifiedOutside

noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace PositivityTheory.Lit1.GF

theorem globalFiniteness : ReciprocityTheory.Gal.GlobalFiniteness := by
  intro F Ω _ _ _ _ _ l hl r M _ _ _ _ _ S rhoS hr hS hc
  obtain ⟨A, _, hAf, hn, ⟨e1⟩, ⟨e2⟩, en⟩ := PositivityTheory.Lit1.GFTransport.cohDict S rhoS hc
  refine ⟨?_, ?_, ?_, fun hl2 n hn3 => ?_⟩
  · exact Finite.of_injective (fun x : H0 rhoS => (x : M)) Subtype.val_injective
  · have := GlobalTheory.CompanionTheory.GSFin.finite_cohomology_one F Ω l r S hS A hAf hn
    exact Finite.of_equiv _ e1.toEquiv.symm
  · have := PositivityTheory.Lit1.GFParts.finite_H2_torsion_module F Ω l r S hS A hAf hn
    exact Finite.of_equiv _ e2.toEquiv.symm
  · have := PositivityTheory.Lit1.GFParts.subsingleton_hn F Ω l r S hS hl2 A hAf hn n hn3
    obtain ⟨e⟩ := en n
    exact e.toEquiv.subsingleton

end PositivityTheory.Lit1.GF
