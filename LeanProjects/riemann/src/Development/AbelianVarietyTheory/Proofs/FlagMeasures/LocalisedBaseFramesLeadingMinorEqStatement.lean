import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalisedBaseFramesLeadingMinorEq
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localised_base_frames_leading_minor_eq : ∀ (D : D7) (Z : LocDat D) (p : PlF D) {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T)
    (F' : LFlag (VS D) D.R.rS T') (Tn T'n : ℕ) (P : Formalism.MainNotions.S.LocNG.FPair (locH Z p) D.R.rS),
    AtBase Z p F F' Tn T'n P → ∀ l : ℕ, P.Dm l =
      (∏ a : Fin (D.R.rS + 1), if a.val < l then (Z.M p).L.cj (frFac Z.δ p a) * frFac Z.δ p a else 1) *
        (D.s.atP p).ιE (Formalism.MainNotions.S.Dl F.fl F'.fl l) := by
  first | exact @GlobalTheory.LocMinor.leadMinor_atBase | exact GlobalTheory.LocMinor.leadMinor_atBase | (intros; apply GlobalTheory.LocMinor.leadMinor_atBase <;> assumption)
