import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.IdxCount
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.IdxAbs

noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain

variable {D : D7}

theorem piH_mem_KvH (X : HidaSetting D) (u : D.what₂.Word) (v : HeightOneSpectrum (𝓞 X.B.I.F))
    (z : Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) (hz : z ∈ KHg X u) :
    piH X u v z ∈ KvH X u v := by
  have h : (z : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) ∈
      Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := hz
  rw [Kf, Subgroup.mem_iInf] at h
  exact h v

def SurjH : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (u : D.what₂.Word),
    X.MeasTie hb → X.LevelSubgroupNormalized → ∀ f : ∀ p : TypX X, KvH X u p.1,
      ∃ z ∈ KHg X u, ∀ p : TypX X, piH X u p.1 z = f p

def LocH : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (u : D.what₂.Word),
    X.MeasTie hb → X.LevelSubgroupNormalized → ∀ z ∈ KHg X u,
      (∀ p : TypX X, ∃ w ∈ unitaryLevelClosureSubgroup X hb u, piH X u p.1 w = piH X u p.1 z) → z ∈ unitaryLevelClosureSubgroup X hb u

theorem idxProdH_of (hS : SurjH) (hL : LocH) : IdxProdH := by
  intro D X hb hK u hT hLv
  exact PI.MassDataKppVolLemmas.IdxAbs_relIndex (KHg X u) (unitaryLevelClosureSubgroup X hb u) (fun p : TypX X => piH X u p.1)
    (fun p : TypX X => KvH X u p.1) (fun p z hz => piH_mem_KvH X u p.1 z hz)
    (hS X hb hK u hT hLv) (hL X hb hK u hT hLv)

end PIW.MassDataColumns
