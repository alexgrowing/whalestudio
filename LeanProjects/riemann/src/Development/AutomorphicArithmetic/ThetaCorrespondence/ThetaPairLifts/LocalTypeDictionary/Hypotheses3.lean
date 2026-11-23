import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LatticeFramesOfHyps
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.HeckeFormOfDoubling

section
namespace GlobalTheory.PrimIn
structure PublishedThetaConditionTheorems : Prop where
  q1 : GlobalTheory.Hk3.HoweUnram
  q2 : GlobalTheory.Published.CuspRapidDecay
  q3 : GlobalTheory.Published.HarishChandraFinite
  q4 : GlobalTheory.Published.HarishChandraModules
  q5 : GlobalTheory.Published.DiscreteSeriesCover
  q6 : GlobalTheory.Published.CasselmanWallach
  q7 : GlobalTheory.Published.WeilSiegelFormulaUnitary
  sw : GlobalTheory.Published.SiegelWeilUnitaryConvergent
  q9 : _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals
  q10 : GlobalTheory.Published.UnramifiedDoublingGL
  q11 : GlobalTheory.Published.BernsteinZelevinskyFiniteness
  q12 : GlobalTheory.Published.GreenCuspidal
  q13 : GlobalTheory.Published.WeilRepresentationUnitaryPair
  q14 : GlobalTheory.Published.SchurOrthogonalitySquareIntegrable
theorem PublishedThetaConditionTheorems.q8 (h : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems) : ∀ D : Formalism.BasicNotions.D7, GlobalTheory.Core.Rk.SW.HeckeFormNS D := fun D =>
  GlobalTheory.Core.Rk.SW.heckeFormNS_of_heckeForm
    (_root_.GlobalTheory.Core.Rk.IP.heckeForm_of_doubling' h.q13 h.q2 h.q7 h.sw h.q9 h.q10 D)
end GlobalTheory.PrimIn
end
