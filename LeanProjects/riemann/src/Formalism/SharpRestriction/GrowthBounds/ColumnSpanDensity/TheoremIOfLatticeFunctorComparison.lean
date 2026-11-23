import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.TheoremIOfIntermediateBounds
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.LatticeCountPrimeMonoLevel
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.MidMeanOf
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.ThrLPOf
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.ThresholdFixedWeightFacts
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.ThresholdDensityFacts
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.ThresholdFinalFacts
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FinrankLetter
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.RhoUpperBoundSmallDepth
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.EdgeIndep
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.InvariantSectionsTransportGL
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.RhoSumBoundOfMapsSplitting
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.LatticeMapsOfFunctorComparison
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FunctorComparisonOfSingleWeightFacts
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.SingleWeightOfModelIdentification
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.ModelIdentificationOfExplicitMap
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.ResidueClassCountOfTensorBasisInclusion
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.RestTensor
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.HLepolyTr
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.LpRingIndepOf
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.RestOIso
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.BlockSplit
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.CloudBoundOfPropAndWeylDimension
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.CloudPropOfMapsBasis
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.TensorBoundOfOrderBound

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

theorem tools_of_admitted_statements (D : Formalism.BasicNotions.D7) (hA : AdmBE D) : AdmT D := by
  obtain ⟨T0, _, h0⟩ := hA 4 (by norm_num)
  obtain ⟨T1, _, h1⟩ := h0 T0 le_rfl
  obtain ⟨T2, _, h2⟩ := h1 T1 T1 T1 le_rfl le_rfl le_rfl
  obtain ⟨CA, Ckap, Ct, Cs, _, _, _, _, hAdm⟩ := h2 T2 le_rfl
  exact hAdm.2.2.2.2

theorem thrFM (K : Cst) (hK : K.Pos) : TransportedAlt K (fun _ => FM K) :=
  (threshold_fixed_weight_facts K hK).and ((threshold_density_facts K hK).and ((threshold_mean_kappa_facts K hK).and (threshold_final_facts K hK)))

theorem restEdge : RestEdge := restEdge_of restFunct

theorem blockSplit' : BlockSplit := fun _ _ _ _ _ _ n z hz A h => KP.blockSplit n z hz A h

theorem second_estimate_of_restrictions (D : Formalism.BasicNotions.D7) (hR : LPRingIndep) (h61a : RhoSumLowerBoundEdge) (h62 : CloudWeightLowerBound) (h63 : ResidueClassCount) :
    SecondPartClosed D := by
  intro hA
  have hT := tools_of_admitted_statements D hA
  have h16 : PairedPathIndependence D := hT.2.2.2.2.2.2.2.2.2.2.2
  have hD : RestDims := restDims_of D h16.1 h16.2
  exact theorem_I_of_intermediate_bounds D FM hR (midLP_of rho_lower_bound_large_conductor h62 h63)
    (fun K hK => midMean_of D h61a rho_upper_bound_small_depth restEdge hD K hK) thrLP thrFM hA

theorem theorem_I_of_finer_open_statements (D : Formalism.BasicNotions.D7) (hR : LPRingIndep) (h61 : LatticeFunctorComparison) (hC : RestCloudMaps) : SecondPartClosed D := by
  intro hA
  have hT := tools_of_admitted_statements D hA
  have h16 : PairedPathIndependence D := hT.2.2.2.2.2.2.2.2.2.2.2
  have h13 : TypeDecompositionsCommute D := hT.2.2.2.2.2.2.2.2.1
  exact second_estimate_of_restrictions D hR (rho_sum_bound_of_maps_splitting (lattice_maps_of_functor_comparison h61) blockSplit') (cloud_bound_of_maps hC h13.2.2.1 h13.1 h16.2)
    (tensor_bound_of_order_bound restTensor restOrdBound h13.1 h13.2.1) hA

theorem theorem_I_of_lattice_functor_comparison (D : Formalism.BasicNotions.D7) (h61 : LatticeFunctorComparison) (hC : RestCloudMaps) : SecondPartClosed D := by
  intro hA
  have h12 : NestedTypeBound D := (tools_of_admitted_statements D hA).2.2.2.2.2.2.2.1
  exact theorem_I_of_finer_open_statements D (lpRingIndep_of'' h12.1 restOIso) h61 hC hA

theorem theorem_I_of_model_identification (D : Formalism.BasicNotions.D7) (hTie : TwoLetterModelIdentification) (hC : RestCloudMaps) : SecondPartClosed D :=
  theorem_I_of_lattice_functor_comparison D (functor_comparison_of_single_weight_facts (single_weight_of_model_identification hTie)) hC

theorem theorem_I_of_explicit_minor_map (D : Formalism.BasicNotions.D7) (hPsi : TiePsi) (hC : RestCloudMaps) : SecondPartClosed D :=
  theorem_I_of_model_identification D (model_identification_of_explicit_map hPsi) hC

end Formalism.MainNotions.flipOneThree.Pf
