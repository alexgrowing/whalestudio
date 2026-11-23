import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DoublingInputsImply
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ConditionOfMemberHypotheses
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MultiplicityCoverHypotheses
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedSiegelWeilIdentityOfSiegelWeilFormula
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedLocalMultiplicityEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DoublingInputsImplyStatement

section
open GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.LiteralAutomorphy
namespace GlobalTheory.Mem
theorem member_hodgeHyp_of_localInputs_rationalWeights : _root_.GlobalTheory.Mem.LiteralAutomorphy.MemberHypotheses → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitarySchrodinger → GlobalTheory.Published.SiegelEisensteinContinuation → _root_.GlobalTheory.Published.UnusedSlot72 → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.SchurOrthogonalitySquareIntegrable → RowRatW → _root_.GlobalTheory.Mem.Top.Bl.MultiplicityCoverHypotheses :=
  fun m hm dc cw ws sw e1 e2 ud bz so r =>
    _root_.GlobalTheory.Mem.LiteralAutomorphy.condition_of_memberHypotheses dc (_root_.GlobalTheory.twisted_siegel_weil_identity_of_siegel_weil_formula GlobalTheory.Hk3.howeUnram_holds m.m3 m.m4 hm dc cw ws sw e1 e2 ud bz m.m14 so) GlobalTheory.Published.HeckeLPartialContinuation_holds
      (_root_.GlobalTheory.Mem.R3.Rw.MultAt.twisted_local_multiplicity_eq m.m1 m.m2 m.m3 m.m4 m.m5 m.m6 m.m7 m.m12 m.m13 m.m14) r
end GlobalTheory.Mem
end

section
open GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.LiteralAutomorphy
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compatibleSystem_member_rationalWeights : _root_.GlobalTheory.Mem.LiteralAutomorphy.MemberHypotheses → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitarySchrodinger → GlobalTheory.Published.SiegelEisensteinContinuation → _root_.GlobalTheory.Published.UnusedSlot72 → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.SchurOrthogonalitySquareIntegrable → RowRatW → _root_.GlobalTheory.Mem.Top.Bl.MultiplicityCoverHypotheses := by
  first | exact @_root_.GlobalTheory.Mem.member_hodgeHyp_of_localInputs_rationalWeights | exact _root_.GlobalTheory.Mem.member_hodgeHyp_of_localInputs_rationalWeights | (intros; apply _root_.GlobalTheory.Mem.member_hodgeHyp_of_localInputs_rationalWeights <;> assumption)
end
