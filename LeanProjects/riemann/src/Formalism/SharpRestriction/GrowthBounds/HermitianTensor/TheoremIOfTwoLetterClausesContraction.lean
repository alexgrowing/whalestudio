import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.NuOfWtPQCast
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CloudA
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CloudB
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CloudC
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CloudIso

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

theorem cloud_maps_of_contraction (hQ : ContractionStandardLattice) (hCD : CartanDomain) (hCO : CartanOnto) (hIncl : DualHeightInclusion) : RestCloudMaps :=
  restCloudMaps_of (restCloudLat_of (cloudOne_of hQ) hCO (cloudIso hCD hCO)) hIncl

theorem theorem_I_of_two_letter_clauses_contraction (D : Formalism.BasicNotions.D7) (h1 : ExplicitMapInjective) (h2 : ExplicitMapOntoTwoLetters) (h5 : TwoLetterLatticeGaussInverse) (hQ : ContractionStandardLattice) : SecondPartClosed D := by
  intro hA
  have hT := tools_of_admitted_statements D hA
  have h11 : GradedLatticeStable D := hT.2.2.2.2.2.2.1
  have h13 : TypeDecompositionsCommute D := hT.2.2.2.2.2.2.2.2.1
  have h16 : PairedPathIndependence D := hT.2.2.2.2.2.2.2.2.2.2.2
  exact theorem_I_of_explicit_minor_map D (tiePsi_of D h1 h2 h5 h11.2 h16.1) (cloud_maps_of_contraction hQ h11.1 h11.2 h13.2.1) hA

end Formalism.MainNotions.flipOneThree.Pf
