import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.IndexOffRange
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.KcolEqPathWord
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.PeBnOfLt
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.ExtendByZeroRestrictOfVanish

namespace Formalism.MainNotions.G.ColumnFamilies

theorem admissible_standardPath_basis (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.PathBasisOverRing D :=
  word_basis_of_path_restrictions D restPathTo restPathFrom restStd restPsi restPol

theorem admissible_polynomial_basis (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.PathColumnBasis D := Formalism.MainNotions.CovariantDegrees.path_basis_of_field_basis D (admissible_standardPath_basis D)

theorem admissible_polynomial_basis_prov (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.HyperplaneRank D := admissible_polynomial_basis D

end Formalism.MainNotions.G.ColumnFamilies
