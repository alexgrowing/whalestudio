import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.L2SGWfEqOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.SigmaDecomposition
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.SchurOrthogonalityRelations
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.SubgroupHypothesisHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.RepresentationUnitary
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.DecayR
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.HaarWN
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.NotMidCases
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.ProductDecompositionHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.OpnContinuous
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.NilradicalHaarUnique
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.NilradicalHalfSumNonneg
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.PsiGenNorm
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.AeProductMemUnipotentAndNilradical
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.RepresentationContinuous
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.StarOfInv
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.WavePacketL1L2OfHypotheses
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.AKindR
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.NilradicalUnimodularConjInvariant
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.ANonzeroOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.UnipotentRightInvariance

noncomputable section

open Formalism.L2.SG.SplitPrimeNormLemmas

namespace WlocSk

theorem unipotent_set_compact : PtD.UWComp := fun _ _ z hz hT => HM.compactW z hz hT

theorem nIntDecay_of_chart (hNC : NChart) : NIntDecay := nIntDecay_of (nCoordHaar_of hNC nilradical_haar_unique)

theorem aInt_of_chart (hNC : NChart) : AInt :=
  PtD.wave_packet_integrable sigma_decomposition DecayR.decay_estimate DecayR.reproducing_formula_holds subgroup_hypothesis_holds representation_unitary
    (nIntDecay_of_chart hNC) unipotent_set_compact

theorem aCont_of_chart (hNC : NChart) : ACont :=
  PtD.wave_packet_continuous sigma_decomposition DecayR.decay_estimate DecayR.reproducing_formula_holds subgroup_hypothesis_holds representation_unitary
    (nIntDecay_of_chart hNC) unipotent_set_compact

theorem aBound_of_chart (hNC : NChart) : ABound :=
  PtD.aBound_of sigma_decomposition DecayR.decay_estimate DecayR.reproducing_formula_holds subgroup_hypothesis_holds representation_unitary
    (nIntDecay_of_chart hNC) unipotent_set_compact

theorem aEquiv_of_charts (hNC : NChart) (hWR : WRightInv) (hNU : NUnimod) : AEquiv :=
  aEquiv_of subgroup_hypothesis_holds representation_unitary sigma_decomposition hWR hNU (aInt_of_chart hNC)

theorem wave_packet_weighted_integrable : AWeighted :=
  AQ.aWeighted_of subgroup_hypothesis_holds representation_unitary sigma_decomposition product_decomposition_holds DecayR.decay_estimate

theorem aKind_of_chart (hNC : NChart) : AKind :=
  AK.aKind_of sigma_decomposition subgroup_hypothesis_holds (aBound_of_chart hNC) DecayR.decay_estimate Port.schur_orthogonality_relations

theorem aReprod_of_chart (hNC : NChart) : AReprod :=
  AK.aReprod_of sigma_decomposition subgroup_hypothesis_holds (aBound_of_chart hNC) DecayR.reproducing_formula_holds

theorem wave_packet_l1_l2_of_nilpotent_chart (hNC : NChart) (hWR : WRightInv) : WavePacketL1L2 :=
  AQ.wave_packet_l1_l2_of_hypotheses subgroup_hypothesis_holds representation_unitary sigma_decomposition product_decomposition_holds DecayR.decay_estimate hWR nilradical_unimodular_conj_invariant
    (aBound_of_chart hNC)

theorem aNonzero_of_charts (hNC : NChart) (hWR : WRightInv) : ANonzero :=
  ANz.aNonzero_of subgroup_hypothesis_holds representation_unitary product_decomposition_holds (aEquiv_of_charts hNC hWR nilradical_unimodular_conj_invariant)
    (aCont_of_chart hNC)

theorem wlocExists_of_charts (hNC : NChart) (hWR : WRightInv)
    (hR : Formalism.L2.SG.HCReprodM.HCReprodDSm) : WlocExists :=
  scWlocExists_of haar_measure_unipotent_nilradical (aEquiv_of_charts hNC hWR nilradical_unimodular_conj_invariant) (aCont_of_chart hNC)
    (aKind_of_chart hNC) (aReprod_of_chart hNC) (wave_packet_l1_l2_of_nilpotent_chart hNC hWR) wave_packet_weighted_integrable
    (aNonzero_of_charts hNC hWR) hR

theorem scWlocExists_of_chart (hNC : NChart) (hR : Formalism.L2.SG.HCReprodM.HCReprodDSm) : WlocExists :=
  wlocExists_of_charts hNC unipotent_right_invariance hR

end WlocSk
