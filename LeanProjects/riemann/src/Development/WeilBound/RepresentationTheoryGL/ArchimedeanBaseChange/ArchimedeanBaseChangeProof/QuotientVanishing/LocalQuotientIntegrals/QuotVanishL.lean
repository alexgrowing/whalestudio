import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocVanishOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NilradicalChangeOfVariables
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulVecMemUniRad

open MeasureTheory

namespace PositivityTheory.Rg.BcB.CV

theorem quotVanishL : GlobalTheory.CompanionTheory.LocVan.QuotVanish := by
  intro n _ _ μ _ d μd _ W₁ W₂ hs _ hW h1 h2 F hF hT hK h0
  letI : MeasurableSpace (nilrad W₁ W₂) := borel _
  haveI : BorelSpace (nilrad W₁ W₂) := ⟨rfl⟩
  haveI : LocallyCompactSpace (nilrad W₁ W₂) := (nilrad W₁ W₂).closed_of_finiteDimensional.isClosedEmbedding_subtypeVal.locallyCompactSpace
  refine GlobalTheory.CompanionTheory.QuotVan.quotVanish n μ d μd W₁ W₂ hW Measure.addHaar F hs h1 h2 hF hT hK fun q _ => ?_
  simp only [GlobalTheory.CompanionTheory.QuotVan.uOf_eq]
  exact h0 _ q

theorem locVanish : LocVanish := GlobalTheory.CompanionTheory.LocVan.locVanish_of GlobalTheory.CompanionTheory.LocVan.nilChange_of_flag quotVanishL

end PositivityTheory.Rg.BcB.CV
