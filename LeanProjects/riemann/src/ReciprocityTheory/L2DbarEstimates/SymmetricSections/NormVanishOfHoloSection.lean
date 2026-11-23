import ReciprocityTheory.L2DbarEstimates.SymmetricSections.NormVanishOfParts
import ReciprocityTheory.L2DbarEstimates.SymmetricSections.RemovableFinset
import ReciprocityTheory.L2DbarEstimates.SymmetricSections.EsymmZero
import ReciprocityTheory.L2DbarEstimates.SymmetricSections.LineFinite
import ReciprocityTheory.L2DbarEstimates.SymmetricSections.SymmGrowth
import ReciprocityTheory.L2DbarEstimates.SymmetricSections.SymmVanish
import ReciprocityTheory.L2DbarEstimates.SymmetricSections.SymmDiff
import ReciprocityTheory.L2DbarEstimates.SymmetricSections.Section

namespace ReciprocityTheory.L2DbarEstimates.Norm

universe u

theorem normVanish_of_holoSection (hsec : holoSectionStatement.{u}) : normVanishStatement.{u} :=
  normVanish_of_parts lineVanish esymmZero (symmDiff_of_holoSection hsec) symmVanish symmGrowth
    lineFinite

theorem normVanish : normVanishStatement.{u} := normVanish_of_holoSection holoSection

end ReciprocityTheory.L2DbarEstimates.Norm
