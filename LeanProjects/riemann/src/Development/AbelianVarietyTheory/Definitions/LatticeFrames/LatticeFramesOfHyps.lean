import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Params
import Development.AbelianVarietyTheory.Definitions.Divisors.Hypotheses2
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeFormOfDoubling

namespace GlobalTheory.PrimIn

structure Hypotheses3 : Prop where
  q1 : GlobalTheory.Hk3.HoweUnram
  q2 : GlobalTheory.Published.CuspRapidDecay
  q3 : GlobalTheory.Published.HarishChandraFinite
  q4 : GlobalTheory.Published.HarishChandraModules
  q5 : GlobalTheory.Published.DiscreteSeriesCover
  q6 : GlobalTheory.Published.CasselmanWallach
  q7 : GlobalTheory.Published.WeilSiegelFormulaUnitary
  sw : GlobalTheory.Published.SiegelWeilUnitaryConvergent
  q9 : GlobalTheory.Published.DoublingMethod
  q10 : GlobalTheory.Published.UnramifiedDoublingGL
  q11 : GlobalTheory.Published.BernsteinZelevinskyFiniteness
  q12 : GlobalTheory.Published.GreenCuspidal
  q13 : GlobalTheory.Published.WeilRepresentationUnitaryPair
  q14 : GlobalTheory.Published.SchurOrthogonalitySquareIntegrable

theorem Hypotheses3.q8 (h : Hypotheses3) : ∀ D : Formalism.BasicNotions.D7, GlobalTheory.Core.Rk.SW.HeckeFormNS D := fun D =>
  GlobalTheory.Core.Rk.SW.heckeFormNS_of_heckeForm
    (GlobalTheory.Core.Rk.IP.heckeForm_of_doubling₂ h.q13 h.q2 h.q7 h.sw h.q9 h.q10 D)

theorem Hypotheses3.of_classicalTheorems2 (h : Hypotheses2) : Hypotheses3 :=
  ⟨h.q1, h.q2, h.q3, h.q4, h.q5, h.q6, h.q7, h.q8, h.q9, h.q10, h.q11, h.q12, h.q13, h.q14⟩

theorem Hypotheses3.toHypotheses2 (h : Hypotheses3) : Hypotheses2 :=
  ⟨h.q1, h.q2, h.q3, h.q4, h.q5, h.q6, h.q7, h.sw, h.q9, h.q10, h.q11, h.q12, h.q13, h.q14⟩

example : Hypotheses3 ↔ Hypotheses2 := ⟨Hypotheses3.toHypotheses2, Hypotheses3.of_classicalTheorems2⟩

example (h : Hypotheses3) (D : Formalism.BasicNotions.D7) : GlobalTheory.Core.Rk.SW.HeckeFormNS D := h.q8 D

end GlobalTheory.PrimIn
