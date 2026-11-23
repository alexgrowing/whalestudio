import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.AdmissiblePolynomialBasisProv
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.AdmissibleWordBasis
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.AdmFourteen
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.AdmissibleExternalProduct
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths
import Formalism.SharpRestriction.GrowthBounds.GLWeightTheory

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.LemmaBAlt Formalism.MainNotions.G.GLWeightTheory

theorem splitting_third_part_holds (D : Formalism.BasicNotions.D7) : DefiniteRankOne D := by
  intro p _ O _ _ _ _ N n _ LL B th M
  exact ⟨lemma_A3_over_domain LL B D word_valuation_bounds (valuation_field D).1 (admissible_standardPath_basis D) (admissible_word_basis D) O th M,
    lemma_A3_over_field LL B D word_valuation_bounds (valuation_field D).1 (admissible_standardPath_basis D) (admissible_word_basis D) (Formalism.MainNotions.G.FF O) th M⟩

theorem splitting_package_holds (D : Formalism.BasicNotions.D7) : Conclusion2 D :=
  ⟨automorphicSideConclusion_of_pathBasis D (admissible_standardPath_basis D), splitting_third_part_holds D, prvB1_of_D7 D, lemma_B2 D,
    nested_sets_lemma_of_admitted D (adm_fourteen D) (admissible_externalProduct D), coefficientDependence D, canonical_translate_jet_identity D⟩

end Formalism.MainNotions.G.ColumnFamilies
