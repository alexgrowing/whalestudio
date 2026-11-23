import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SiegelWeilDoublingAssembly
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Hypotheses3
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DoublingMethodOfEisensteinFacts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SiegelWeilDoublingAssemblyStatement

section
namespace GlobalTheory.PrimIn
theorem twisted_siegel_weil_identity_of_formula :
    GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraFinite →
    GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach →
    GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent →
    GlobalTheory.Published.SiegelEisensteinContinuation → _root_.GlobalTheory.Published.UnusedSlot72 →
    GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness →
    GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.SchurOrthogonalitySquareIntegrable →
    _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems := by
  intro q1 q2 q3 q4 q5 q6 q7 sw e1 e2 q10 q11 q12 q14
  exact ⟨q1, q2, q3, q4, q5, q6, q7, sw, _root_.GlobalTheory.T.doubling_zeta_of_eisenstein_facts q2 e1 e2, q10, q11, q12,
    GlobalTheory.weilRepresentationUnitaryPair, q14⟩
end GlobalTheory.PrimIn
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_siegel_weil_identity : GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → GlobalTheory.Published.SiegelEisensteinContinuation → _root_.GlobalTheory.Published.UnusedSlot72 → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.SchurOrthogonalitySquareIntegrable → _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems := by
  first | exact @_root_.GlobalTheory.PrimIn.twisted_siegel_weil_identity_of_formula | exact _root_.GlobalTheory.PrimIn.twisted_siegel_weil_identity_of_formula | (intros; apply _root_.GlobalTheory.PrimIn.twisted_siegel_weil_identity_of_formula <;> assumption)
end
