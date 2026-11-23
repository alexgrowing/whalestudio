import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.AdmissibleExternalProductOfHyps
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.DisjointRestrictSupportOfDisjoint
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.RenameMulRenameMemSpanProductBasis
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.DominantOfIsHighestWeightVectorPolynomial
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.IsotypicSumInfStandardWordsOutsideEqBot
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.SubProjectorProductMemStrict

namespace Formalism.MainNotions.G.ColumnFamilies

theorem externalProduct_basis : ExternalProductBasis := fun R _ N r K LL B => ⟨linearIndependent_productBasis R N r K LL B, span_productBasis_eq_multihomogeneous R N r K LL B⟩

theorem externalProductHyps (D : Formalism.BasicNotions.D7) : ExternalProductHyps where
  p16 := externalProduct_basis
  e1 := determinant_divisibility
  e2 := polynomialHighestWeight_dominant D
  e3 := projectors_preserve_multidegree
  e5a := polynomialProjectors_commute_nested
  e5b := polynomialProjectors_commute_disjoint
  lowPl := restLowPl_of D (polynomialTypeSums_by_evaluation D) externalProduct_basis
  lowTan := restLowTan_of D (polynomialTypeSums_by_evaluation D) externalProduct_basis
  sum := restJointSum

theorem admissible_externalProduct (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.PairedPathIndependence D := admissible_externalProduct_of_hyps D (externalProductHyps D)

end Formalism.MainNotions.G.ColumnFamilies
