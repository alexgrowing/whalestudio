import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge

def muSv {D : D7} (X : HidaSetting D) (w : D.what₂.Word) (p : TypX X) : ℝ :=
  ((X.measW w).μSv p.1 (Subtype.val ⁻¹' Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1)).toReal

def muSvpp {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (w : D.what₂.Word) (p : TypX X) : ℝ :=
  ((X.measW w).μSv p.1 (Subtype.val ⁻¹' compSet X.B.I.cm.sig X.B.I.J (K2u X hb w) p.1)).toReal

def muSf {D : D7} (X : HidaSetting D) (w : D.what₂.Word) : ℝ :=
  ((X.measW w).μSf (Subtype.val ⁻¹' (Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :
    Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)))).toReal

def muNf {D : D7} (X : HidaSetting D) (w : D.what₂.Word) : ℝ :=
  ((X.measW w).μNf (Subtype.val ⁻¹' (Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :
    Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)))).toReal

def muHf {D : D7} (X : HidaSetting D) (w : D.what₂.Word) : ℝ :=
  ((X.measW w).μHf (Subtype.val ⁻¹' (Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :
    Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)))).toReal

def muHfpp {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (w : D.what₂.Word) : ℝ :=
  ((X.measW w).μHf (Subtype.val ⁻¹' K2u X hb w)).toReal

def TypedNe : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.MeasTie hb → X.LevelSubgroupNormalized →
    ∀ (w : D.what₂.Word) (p : TypX X), muSv X w p ≠ 0

def GlobLevelS : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.MeasTie hb → X.LevelSubgroupNormalized →
    ∀ w : D.what₂.Word, muSf X w = muNf X w * muHf X w

def RatioH : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → X.MeasTie hb → X.LevelSubgroupNormalized →
    ∀ w : D.what₂.Word,
      muHfpp X hb w * ∏ p : TypX X, muSv X w p = muHf X w * ∏ p : TypX X, muSvpp X hb w p

end MassDataLevelSSteps
