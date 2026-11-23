import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.PairVal
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RelativeIndexFlags.VolumeIndexRepresentationNonzero
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RelativeIndexFlags.StabAutConjHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.VolumeIndexBCongruence
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RelativeIndexFlags.UnipotentConjIndexHolds

open Formalism.L2.SG.Pf.RelativeIndexFlags

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem volume_index_representation_of_data (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) (F0 : Formalism.MainNotions.S.FlagG (Formalism.MainNotions.S.VS D) D.R.rS ((Formalism.MainNotions.S.Lat.Tu D u : ℕ) : D.host.E)) (what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (Formalism.MainNotions.S.VS D).V)) (hS : Formalism.L2.SG.TermDef.TermStable D u u') (hE : Formalism.L2.SG.TermDef.TermEqIff D u u') (hF : Formalism.L2.SG.TermDef.TermFun D u u') (hP : Formalism.MainNotions.S.Lat.PrimeHyp D u (Formalism.MainNotions.S.Lat.Tu D u')) (hsig : (Formalism.MainNotions.S.VS D).SigOK) (hrows : Formalism.MainNotions.S.IsRowReps D F0 what₂)
    (hFin : VolIdxFinP D u u' F0 what₂) :
    Formalism.L2.SG.Pf.RelativeIndexFlags.VolumeIndexRepresentationNonzero D u u' F0 what₂ :=
  volume_index_representation_of_finite D u u' F0 what₂ (stabAutConj_holds D u u' F0 what₂ hE hrows) hFin
    (unipotent_conj_index_holds (D.R.rS + 1) D.host.E)
