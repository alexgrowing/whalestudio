import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UnitaryThreeAutomorphyOfInputs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HidaU
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PointTheoremBaseObject
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.CoefIsCoef

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.Mem.LiteralAutomorphy
namespace UpperTheory.V.W
theorem cohP_alt (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) : Pa.CohP :=
  ⟨hN.coh.lf, hN.coh.lt, hN.coh.le, hN.coh.gf, hN.coh.ge, hN.coh.gw, hN.coh.pt, GlobalTheory.Published.TameLocal_of_duality hN.coh.lt⟩
theorem global_compat_printed_of_literal_automorphy_n (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) : GC.Hypotheses₂ :=
  ⟨⟨hN.coh.lf, hN.coh.lt, hN.coh.le, hN.coh.gf, hN.coh.ge, hN.coh.pt⟩, hN.coh.uo, hN.coh.gw⟩
theorem locPrints_of_litN (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) : Loc.LocalPublishedTheorems :=
  ⟨hN.coh.lfK, hN.coh.ltK, hN.coh.leK, hN.coh.lf, hN.coh.lt, hN.coh.le, hN.coh.bk⟩
theorem local_class_field_theory_all_of_literal_automorphy (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) : LocCFTAll := locCFT hN.aut.art (_root_.UpperTheory.V.W.cohP_alt hN)
theorem modularity_unitary_of_automorphy_hida_unitary (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (hP : Pa.PfromAut) (hH : _root_.UpperTheory.V.W.HidaUAlt) : _root_.UpperTheory.V.W.ModUAlt := _root_.UpperTheory.V.W.modU_of_printsH (_root_.UpperTheory.V.W.cohP_alt hN) (_root_.UpperTheory.V.W.local_class_field_theory_all_of_literal_automorphy hN) hP hH
end UpperTheory.V.W
end
