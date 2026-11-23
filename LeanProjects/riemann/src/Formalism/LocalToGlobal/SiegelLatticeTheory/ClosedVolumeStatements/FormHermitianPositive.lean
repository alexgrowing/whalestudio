import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictK
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ColPhaseCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ChiNCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.AdmNPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RankOneTensors
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TermsAtPtFinite

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.TermOp Formalism.L2.SG.NormCut

namespace Formalism.L2.SG.Closed

section Cols

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Lat.Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}

theorem TermK_holds (cs : ColSys X u what₂) (cs' : ColSys X u' rows') : TermK F0 F0' cs cs' :=
  Formalism.L2.SG.Pf.termK X cs cs'

theorem ModGAt_holds (X : Formalism.L2.SG.HidaSetting.HidaSetting D) : ModGAt X := Formalism.L2.SG.Pf.modGAt X

theorem AdmN_holds (cs : ColSys X u what₂) (cs' : ColSys X u' rows') (hTF : FrameTie X u u' F0 F0') :
    AdmN F0 F0' cs cs' :=
  adm_norm_of_fixed_frames cs cs' hTF (TermK_holds cs cs') (ModGAt_holds X)

theorem AdmPar_holds (cs : ColSys X u what₂) (cs' : ColSys X u' rows') (hTF : FrameTie X u u' F0 F0') :
    AdmPar F0 F0' cs cs' :=
  adm_parity_of_norm cs cs' (TermK_holds cs cs') (AdmN_holds cs cs' hTF)

end Cols

theorem TermsAtFinite_holds (D : D7) (u u' : D.what₂.Word) : Formalism.L2.SG.TermDef.TermsAtFinite D u u' :=
  terms_at_point_finite D u u'

end Formalism.L2.SG.Closed
