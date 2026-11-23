import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.AdmissiblePolynomialBasisProv
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.AdmissibleWordBasis
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.ToralGalois
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.BoundOneTwo
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.AdmFourteen
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.AdmissibleLowerSetSpan
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.AdmissibleExternalProduct
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.LatticeGeneratedLowestWeight
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.SplittingThirdPartHolds
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.BrCore
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.AdmissibleThmB1
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.AdmissibleThmB2
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.AdmissibleB7
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.AdmissibleThmC3

namespace Formalism.MainNotions.G.ColumnFamilies.Top

open Formalism.MainNotions.CovariantDegrees

theorem b1 (D : Formalism.BasicNotions.D7) : PathPairCorrespondence D := path_pair_correspondence D
theorem b2 (D : Formalism.BasicNotions.D7) : admB2 D := admissible_standard_basis D
theorem b3 (D : Formalism.BasicNotions.D7) : admB3 D := admissible_thm_B1 D
theorem b4 (D : Formalism.BasicNotions.D7) : ColumnFamilyLowerSet D := admissible_thm_B2 D
theorem b5 (D : Formalism.BasicNotions.D7) : GenericProjectionCriterion D := admissible_thm_B3 D
theorem b6 (D : Formalism.BasicNotions.D7) : ColumnFamilyClosure D := column_family_closure D
theorem b7 (D : Formalism.BasicNotions.D7) : TensorColumnFamily D := admissible_B7 D
theorem b8 (D : Formalism.BasicNotions.D7) : BranchingColumnFamily D := admissible_thm_C3 D
theorem b9 (D : Formalism.BasicNotions.D7) : GlobalSectionsSchur D := global_sections_schur D
theorem b10 (D : Formalism.BasicNotions.D7) : BracketPolynomialSpan D := bracket_polynomial_span D
theorem b11 (D : Formalism.BasicNotions.D7) : GradedLatticeStable D := adm_eleven D
theorem b12 (D : Formalism.BasicNotions.D7) : NestedTypeBound D := adm_twelve D
theorem b14 (D : Formalism.BasicNotions.D7) : JointComponentsPaths D := adm_fourteen D
theorem b15 (D : Formalism.BasicNotions.D7) : SaturatedLowerSetSpan D := admissible_lowerSet_span D
theorem b16 (D : Formalism.BasicNotions.D7) : PairedPathIndependence D := admissible_externalProduct D
theorem b17 (D : Formalism.BasicNotions.D7) : PathBasisOverRing D := admissible_standardPath_basis D
theorem b18 (D : Formalism.BasicNotions.D7) : FirstLettersLowerSet D := admissible_word_basis D
theorem b19 (D : Formalism.BasicNotions.D7) : WeylDualityLattice D := admissible_lattice_biduality D
theorem a2 (D : Formalism.BasicNotions.D7) : PathColumnBasis D := admissible_polynomial_basis D
theorem HyperplaneRank (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.HyperplaneRank D := admissible_polynomial_basis_prov D
theorem Conclusion2 (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.Conclusion2 D := splitting_package_holds D

end Formalism.MainNotions.G.ColumnFamilies.Top
