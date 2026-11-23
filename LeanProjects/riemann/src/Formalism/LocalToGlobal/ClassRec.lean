import Formalism.LocalToGlobal.ClassS
import Formalism.LocalToGlobal.ClassSK
import Formalism.LocalToGlobal.ClassSLinks
import Formalism.LocalToGlobal.ClassSR
import Formalism.LocalToGlobal.HilbertRowConditions.RowPinMin
import Formalism.LocalToGlobal.RatioJoints.CharacterProductEqOne
import Formalism.LocalToGlobal.UnitaryNorms.DatumS
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeilEq

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions

namespace Formalism.L2

section

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC}

structure RecT (ex : Extra D L hT Gi Gl K Y cX) where

  T : TiedDataSK ex

  pin : Rows.RowPinMin T

  joints : JointsS T.toTiedDataS

  host : HostDatumS T.toTiedDataS

  weq : Theta.WeilCompatibleEquivariance T.toTiedDataS.theta.W

def TiedRec (ex : Extra D L hT Gi Gl K Y cX) : Prop := Nonempty (RecT ex)

theorem TiedRec.tiedSK {ex : Extra D L hT Gi Gl K Y cX} (h : TiedRec ex) : LinkedFamilyKernelCondition ex :=
  let ⟨R⟩ := h; ⟨R.T⟩

end

def LayerTwoFamilyClass : FamClass := fun {_} Fm =>
  (∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, TiedRec (Fm.ex x hx i)) ∧ LinkedFamiliesAligned Fm

theorem LayerTwoFamilyClass.c2sk {eps : ℝ} {Fm : FamP eps} (h : LayerTwoFamilyClass Fm) : LinkedFamiliesKernelFrame Fm := by
  obtain ⟨⟨x0, h⟩, _⟩ := h
  exact ⟨x0, fun x hx hx0 i => (h x hx hx0 i).tiedSK⟩

theorem LayerTwoFamilyClass.c2s {eps : ℝ} {Fm : FamP eps} (h : LayerTwoFamilyClass Fm) : LinkedFamiliesLevelClass Fm := h.c2sk.c2s

theorem LayerTwoFamilyClass.c2sa {eps : ℝ} {Fm : FamP eps} (h : LayerTwoFamilyClass Fm) : LinkedFamiliesAligned Fm := h.2

theorem gTiedF_of_C2Rec {eps : ℝ} (Fm : FamP eps) (h : LayerTwoFamilyClass Fm) : G.GroupCompatibilityFamily Fm := gTiedF_of_C2S Fm h.c2s

end Formalism.L2
