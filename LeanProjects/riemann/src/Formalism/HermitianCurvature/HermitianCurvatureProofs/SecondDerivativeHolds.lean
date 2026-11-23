import Formalism.HermitianCurvature.StatementPB
import Formalism.HermitianCurvature.HeisenbergConjugationMeasurePreserving
import Formalism.LatticeRigidity.HeightMinimum.SqrtAbsNormLeProd

namespace Formalism.FourierDecayAlt.P.HilbertSchmidtNorm

open Formalism.FourierDecayAlt.PB Finset NumberField

open scoped ComplexOrder ComplexConjugate

open Classical

theorem localCores : Formalism.FourierDecayAlt.PB.LocalCores :=
  ⟨Formalism.FourierDecayAlt.Final.jx_pSDAgree,
   Formalism.FourierDecayAlt.Final.jx_schurProduct,
   Formalism.FourierDecayAlt.Final.jx_productDomination,
   Formalism.FourierDecayAlt.Final.jx_diagScale,
   Formalism.FourierDecayAlt.Final.jx_diagPhase,
   Formalism.FourierDecayAlt.Final.jx_blockDiagPSD,
   Formalism.FourierDecayAlt.Final.jx_productLemma,
   Formalism.FourierDecayAlt.Final.jx_scaleOk,
   Formalism.FourierDecayAlt.Final.jx_phaseOk,
   Formalism.FourierDecayAlt.Final.jx_outsideSysOk,
   Formalism.FourierDecayAlt.Final.jx_outsideDomination,
   Formalism.FourierDecayAlt.Final.jx_localPullback,
   Formalism.FourierDecayAlt.Final.jx_localUnitHeads,
   Formalism.FourierDecayAlt.Final.jx_topPullback,
   Formalism.FourierDecayAlt.Final.jx_topUnitHeads,
   Formalism.FourierDecayAlt.Final.jx_globalOfLocal,
   Formalism.FourierDecayAlt.Final.jx_uniformMajorantOn,
   Formalism.FourierDecayAlt.Final.jx_axiomsFromSystems,
   Formalism.FourierDecayAlt.Final.jx_axiomsFromFamilies,
   Formalism.FourierDecayAlt.Final.jx_kernelOfLocal,
   Formalism.FourierDecayAlt.Final.jx_localKernelPSD,
   Formalism.FourierDecayAlt.Final.tc_domMinOfText,
   Formalism.FourierDecayAlt.Final.tc_domAfterOfLocal,
   Formalism.FourierDecayAlt.Final.gram_determinant_dual_bound_a,
   Formalism.FourierDecayAlt.Final.parahoric_gram_matrix,
   Formalism.FourierDecayAlt.Final.zero_level_ones_vector,
   Formalism.FourierDecayAlt.Final.singleBlockParseval_true,
   Formalism.FourierDecayAlt.Final.theta_equality_first,
   Formalism.FourierDecayAlt.Final.singleBlockThetaProps_true,
   Formalism.FourierDecayAlt.Final.ns_support,
   Formalism.FourierDecayAlt.Final.ns_block_diagonal,
   Formalism.FourierDecayAlt.Final.latticeAverage_of_gram⟩

theorem globalCores : Formalism.FourierDecayAlt.PB.GlobalCores :=
  ⟨Formalism.FourierDecayAlt.Final.tc_theoremAAfter,
   Formalism.FourierDecayAlt.Final.tc_recursionWithDens,
   Formalism.FourierDecayAlt.Final.tc_domScaleTop,
   Formalism.FourierDecayAlt.Final.tc_sumBoundMax,
   Formalism.FourierDecayAlt.Final.tc_recHypScaleTop,
   Formalism.FourierDecayAlt.Final.tc_densSum,
   Formalism.FourierDecayAlt.Final.tc_densLeTwo,
   Formalism.FourierDecayAlt.Final.tc_densSize,
   Formalism.FourierDecayAlt.Final.tc_densChain,
   Formalism.FourierDecayAlt.Final.poisson_summation_text,
   Formalism.FourierDecayAlt.Final.jx_poissonJoint,
   Formalism.FourierDecayAlt.Final.jx_poissonStepJoint,
   Formalism.SA.P.smoothedSumBound,
   Formalism.FourierDecayAlt.Final.lattices_general_position_bound,
   Formalism.FourierDecayAlt.Final.ideals_match,
   Formalism.FourierDecayAlt.Final.ideal_norm_formula,
   Formalism.FourierDecayAlt.Final.field_extension_degree_facts,
   Formalism.FourierDecayAlt.Final.jx_frameProducts,
   Formalism.FourierDecayAlt.Final.jx_xIsLamOne,
   Formalism.FourierDecayAlt.Final.jx_latticeSumsJoint,
   Formalism.FourierDecayAlt.Final.jx_instSizes,
   Formalism.FourierDecayAlt.Final.jx_instLatticeSums,
   Formalism.FourierDecayAlt.Final.sz_sizesMain,
   Formalism.FourierDecayAlt.Final.jx_sizesToRecursion,
   Formalism.FourierDecayAlt.Final.jx_globPositive,
   Formalism.FourierDecayAlt.Final.counting_theorem,
   Formalism.FourierDecayAlt.Final.jx_formGivesMain⟩

end Formalism.FourierDecayAlt.P.HilbertSchmidtNorm

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
