import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ScaledUnitriangularChangeEqLocalImage
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalDiscriminantIsUnit
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaled_unitriangular_change_eq_local_image : ∀ (D : D7) (Z : LocDat D) {T T' : D.host.E} (F0 : LFlag (VS D) D.R.rS T) (F0' : LFlag (VS D) D.R.rS T') (FP : ∀ p : PlF D, Formalism.MainNotions.S.LocNG.FPair (locH Z p) D.R.rS) (G : GFrames (placesOf Z) D.R.rS D.R.k) (c : GCoord Z F0 F0' FP G) (p : PlF D) (N : G.GLV) (m : (G.S p).GLV), (placesOf Z).Ext p N m → ∀ B : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, ((∀ b, N (G.f b) = ∑ a, B a b • G.f a) → ∀ b, (c.c p).e (scaled Z p (fun b => ∑ a, B a b • frame F0 a) b) = m ((G.S p).f b)) ∧ ((∀ b, N (G.f' b) = ∑ a, B a b • G.f' a) → ∀ b, (c.c p).e (scaled Z p (fun b => ∑ a, B a b • frame F0' a) b) = m ((G.S p).f' b)) := by
  first | exact @GlobalTheory.FrCoord.scaled_coord | exact GlobalTheory.FrCoord.scaled_coord | (intros; apply GlobalTheory.FrCoord.scaled_coord <;> assumption)
