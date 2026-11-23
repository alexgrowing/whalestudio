import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.StrongApproxN
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.NLevelHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.BridgeKHolds

noncomputable section

open MeasureTheory NumberField
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets

namespace MassDataMassesW

def FdA {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (FdN : Set X.B.I.Ginf) :
    Set ↥(Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) :=
  {n | ∃ s ∈ FdN, (splitA X.B.I.cm.sig X.B.I.J (n : HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J)).1 = X.toInf hb s ∧
    (splitA X.B.I.cm.sig X.B.I.J (n : HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J)).2 ∈ KX X}

def UnipotentFundamentalDomain : Prop :=
  StrongApproxN → NLevel → BridgeK → SplitIso →
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (u : D.what₂.Word)
    (FdN : Set X.B.I.Ginf), X.MeasTie hb → X.LevelSubgroupNormalized →
    IsSFund X.B.I (Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u) FdN →
    IsFundamentalDomain (ratOf (K := Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)))
      (FdA X hb u FdN) (X.measW u).μN

def N4 : Prop :=
  SplitIso →
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (FdN : Set X.B.I.Ginf),
    (X.measW u).IsTextNorm → X.MeasTie hb →
    IsSFund X.B.I (Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u) FdN →
    (X.measW u).μN (FdA X hb u FdN) =
      X.muN u FdN * (X.measW u).μNf (Subtype.val ⁻¹' (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)))

def UnipotentCoveringCount : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word)
    (𝓕 : Set ↥(Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))),
    (X.measW u).IsTextNorm →
    IsFundamentalDomain (ratOf (K := Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) 𝓕 (X.measW u).μN →
    covol (X.measW u).μN = ((X.measW u).μN 𝓕).toReal

theorem nVolAll_of (hSA : StrongApproxN) (hS : SplitIso) (h3 : UnipotentFundamentalDomain) (h4 : N4) (hc : UnipotentCoveringCount) : NVolAll := by
  intro D X hb hK u FdN hT hL hF
  have hN : (X.measW u).IsTextNorm := X.measW_norm u
  have hfd := h3 hSA NLev.nLevel_holds NBr.bridgeK_holds hS X hb hK u FdN hT hL hF
  have h4' := h4 hS X hb u FdN hN hT hF
  have hc' := hc X u _ hN hfd
  show covol (X.measW u).μN = (X.muN u FdN).toReal *
    ((X.measW u).μNf (Subtype.val ⁻¹' (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)))).toReal
  rw [hc', h4', ENNReal.toReal_mul]

end MassDataMassesW
