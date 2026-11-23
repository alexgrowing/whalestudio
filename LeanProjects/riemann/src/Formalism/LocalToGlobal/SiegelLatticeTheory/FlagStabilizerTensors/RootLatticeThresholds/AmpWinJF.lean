import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWinGlob
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocJEqMeas
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.OoQuotOfNuQPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGPinLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RealDecompL
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LiftOntoCOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LeadingMinors
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WittFlags
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.WeightConstT

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.RealObj

namespace Formalism.L2.SG.Pf.AmpWinJF

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Defs

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} (hI : SIso D.s (sOf hF)) {θ : ℝ} (C : Choice X θ)
  (hB : WuBessel C) (u u' : D.what₂.Word)

def wt {u u' : D.what₂.Word} (t : D.s.Term u u') : Point D.host.E (D.R.rS + 1) := Formalism.L2.SG.PairVal.ptOf (tc hI t)

def AmpPt (ν : X.B.I.Ginf → Measure X.B.I.Ginf) : Prop :=
  ∀ t : D.s.Term u u', D.s.Gterm t ≠ 0 → D.s.relevant t →
    hsNormSq (JtOf hI t) = Formalism.L2.SG.LoopTerm.volRC hI t ^ 2 *
      (Formalism.L2.SG.Pf.OOCore3.sclV Y u u' * hsNormSq (Formalism.L2.SG.Pf.OOCore.OOP u u' ν (wt hI t)))

def PtFacts : Prop :=
  ∀ t : D.s.Term u u', D.s.Gterm t ≠ 0 → D.s.relevant t →
    (∃ g, IsPtRep X u u' (wt hI t) g) ∧ ∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' (wt hI t)) v

def LocUniqT (νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v))) :
    Prop :=
  ∀ t : D.s.Term u u', D.s.Gterm t ≠ 0 → D.s.relevant t → ∀ τ,
    hsNormSq ((locS hB u u' τ).J (Formalism.L2.SG.LoopTerm.nu1 hI C t τ) (Formalism.L2.SG.LoopTerm.gamR hI C t τ)) =
      hsNormSq ((locS hB u u' τ).J ((νl (wt hI t) (vOf X τ)).map
        (Formalism.L2.SG.Pf.LocJEq.Smap C τ ((gamW X u u' (wt hI t)) (vOf X τ))))
        (Formalism.L2.SG.Pf.JointAmplitudePoints.gamP C u u' (wt hI t) τ))

end Defs

section Main

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} (hI : SIso D.s (sOf hF)) {θ : ℝ} (C : Choice X θ)
  (hB : WuBessel C) (u u' : D.what₂.Word)

end Main

section Pts

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} (hI : SIso D.s (sOf hF)) (u u' : D.what₂.Word)

end Pts

section Pin

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} (hI : SIso D.s (sOf hF)) {θ : ℝ} (C : Choice X θ)
  (hB : WuBessel C) (u u' : D.what₂.Word)

theorem levelVolume_pos : 0 < X.volK2 := by
  have h := Formalism.L2.SG.Closed.level_subgroup_properties X
  exact ENNReal.toReal_pos h.2.2.1.ne' h.2.2.2.ne

end Pin

end Formalism.L2.SG.Pf.AmpWinJF
