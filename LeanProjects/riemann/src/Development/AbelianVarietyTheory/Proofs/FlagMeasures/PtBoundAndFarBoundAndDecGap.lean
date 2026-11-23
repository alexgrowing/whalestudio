import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.CuspFrame
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SummableOfSupport
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PtBoundOfDecGap
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeDecayGapOfCompressionFormulaGap
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeCompressionFormulaOfStrictLowestKType

namespace GlobalTheory.Deep

theorem ptBound_and_farBound_and_decGap :
    GlobalTheory.Deep.PtBound ∧ GlobalTheory.Deep.FarBound ∧ GlobalTheory.DSId.DecGap :=
  have hd : GlobalTheory.DSId.DecGap :=
    GlobalTheory.DecGapBound.decGap_of_formulaGap GlobalTheory.Jet.FormGapFree.formulaGap
  have hp : GlobalTheory.Deep.PtBound := GlobalTheory.Deep.ptBound_of_decGap hd
  ⟨hp, GlobalTheory.FarTerms.farBound_of_ptBound hp, hd⟩

end GlobalTheory.Deep
