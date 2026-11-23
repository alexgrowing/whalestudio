import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ColFreePf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictK
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormStepsB
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormCoreGamProdSum

noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace Formalism.L2.SG.NormCut

section Links

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X) {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂) (cs' : ColSys X u' rows')

variable (F0) in

def MassA {w : D.what₂.Word} {rs : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (c : ColSys X w rs) : Prop :=
  ∀ q : {Λ // Λ ∈ rs}, wRow D F0 q.1 = ((Nat.card (Aset TR c q) : ℝ))⁻¹

theorem colPhase_holds (hTF : FrameTie X u u' F0 F0') : ColPhase F0 F0' TR cs cs' (scOf TR cs) (scOf TR cs') := by
  have hN := adm_norm_of_fixed_frames cs cs' hTF (Formalism.L2.SG.Pf.termK X cs cs') (Formalism.L2.SG.Pf.modGAt X)
  have hA := adm_parity_of_norm cs cs' (Formalism.L2.SG.Pf.termK X cs cs') hN
  exact colPhase_of TR cs cs' (leviCols_of TR cs cs' (Formalism.L2.SG.Pf.colLatK X cs) (Formalism.L2.SG.Pf.colLatK X cs') hA)
    (phaseAt_of TR cs cs' (Formalism.L2.SG.Pf.colLatK X cs) (Formalism.L2.SG.Pf.colLatK X cs') hA hN)

theorem colFree_steps (hK : X.LevelSubgroupCharacter) (hR : ColReps hK cs) (hCL : Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u hK)
    (hO : Formalism.L2.SG.Pf.NormSteps.LeviOntoS TR cs) (hRep : Formalism.L2.SG.Pf.NormSteps.ColLatRepS cs hK)
    (hMass : MassA TR F0 cs) : ColFree F0 TR cs (Aset TR cs) (scOf TR cs) := fun q =>
  ⟨colFreeBij_of TR cs hK hR hCL (Formalism.L2.SG.Pf.colLatK X cs) hO hRep q, hMass q⟩

end Links

end Formalism.L2.SG.NormCut
