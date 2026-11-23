import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.VwinOfLeaves
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutEnd3AltAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphyUnramifiedCoefficients
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphyU3OfEndoscopy
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HVFinalU

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.GaloisCohomology UpperTheory.Top GlobalTheory.Mem.LiteralAutomorphy
namespace UpperTheory.V.HV.Core0
open UpperTheory.V.Lit
theorem cohInp_alt (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (hK : ∃ CK : ℝ, LemmaK CK) : U3.CohInp :=
  ⟨_root_.UpperTheory.V.HV.U.locPrints_of_litN hN, hN.coh.pt, hN.coh.gf, hN.coh.ge, hK⟩
theorem automorphyUnramified_of_litN_of_gdEnd (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (hG : _root_.UpperTheory.V.Pr.GdEndAlt) : _root_.UpperTheory.V.Aut.AutomorphyUnramifiedCoefficientsAlt := _root_.UpperTheory.V.Pr.automorphyUnramified_of_locPrints_kisin_gdEnd (_root_.UpperTheory.V.HV.U.locPrints_of_litN hN) hG
end UpperTheory.V.HV.Core0
end
