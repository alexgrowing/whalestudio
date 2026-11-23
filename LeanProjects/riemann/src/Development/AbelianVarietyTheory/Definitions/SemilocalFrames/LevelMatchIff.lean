import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.SettingExistsMeasured
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ColDict
import Formalism.SatakeDualWeyl.StatementC

noncomputable section

open scoped TensorProduct InnerProductSpace
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
open Formalism.MainNotions.S Formalism.L2.SG.SplitPrimeNormLemmas Formalism.L2.SG.ColDict Matrix

namespace GlobalTheory.St

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def WittX (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Prop :=
  (∀ x y, (VS D).hT (wt x) (wt y) = (VS D).hT x y) ∧ (∀ a, wt (X.eX a) = D.sp.hypE a) ∧
    (∀ a, wt (X.fY a) = D.sp.hypF a) ∧ wt (X.zu u) = D.zmOf u

def IsAdeleIso (X : HidaSetting D)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F) : Prop :=
  (∀ x : X.B.I.E, ιA (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) x) =
    Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (X.ιE x)) ∧
  ∀ a, a ∈ IntAf X.B.I.F X.B.I.E ↔ ιA a ∈ IntAf D.host.F D.host.E

def LatMatchH (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u)
    (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)
    (h0 : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : Prop :=
  ∀ x : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F,
    (h0⁻¹).1.1 *ᵥ x ∈
      Formalism.UG.latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
        (Formalism.UG.tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (Formalism.UG.intOE D.host.E)
          (Formalism.UG.intAd D.host.F)) F.cls0.lev.Lb ↔
    (∑ j, ιA.symm (x j) • qA X wt j) ∈ X.B.I.Lf

def LevelKH (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u)
    (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)
    (h0 : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (hK : X.LevelSubgroupCharacter) : Prop :=
  ∀ (h : Hfin X u) (y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F)), RepF X wt ιA (h : X.B.I.Gf) y →
    (h ∈ Ku X u hK ↔ ((h0⁻¹ * y * h0 : Formalism.UG.UPts (Formalism.L2.Forms.sigD D)
        (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : GL _ _) ∈
      F.cls0.lev.U) ∧
    ∀ (hk : h ∈ Ku X u hK) (hy : ((h0⁻¹ * y * h0 : Formalism.UG.UPts (Formalism.L2.Forms.sigD D)
        (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : GL _ _) ∈
        F.cls0.lev.U),
      ((psiK X u hK ⟨h, hk⟩ : ℂˣ) : ℂ) = ((F.cls0.lev.chi ⟨_, hy⟩ : ℂˣ) : ℂ)

theorem levelMatch_iff (X : HidaSetting D) {u : D.what₂.Word} {F : Formalism.L2.Forms.Forms0 D u} (Tr : Transport X u F)
    (hK : X.LevelSubgroupCharacter) :
    LevelMatch X Tr hK ↔ LatMatchH X u F Tr.wt Tr.ιA Tr.h0 ∧ LevelKH X u F Tr.wt Tr.ιA Tr.h0 hK := Iff.rfl

def JOK (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (J : X.Vpi u →ₗ⋆[ℂ] (Formalism.L2.Forms.Fr D 0 (Nat.zero_le _) → ℂ)) : Prop :=
  (∀ s ∈ Hinf X u, ∀ (ξ : X.Vpi u) (y y' : Formalism.L2.Forms.Fr D 0 (Nat.zero_le _)),
    Formalism.L2.Forms.IsTr (sTil X wt s) y' y → J (X.piU u s ξ) y = J ξ y') ∧
  (∀ ξ, J ξ ∈ Formalism.L2.Forms.ValC (Formalism.L2.Forms.gramC (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
    (Formalism.L2.Forms.embT D)) (Formalism.L2.Forms.lamT u 0)) ∧
  ∀ (c : (D.mem u).C.cls 0) (ξ η : X.Vpi u),
    (D.fm u).ipV 0 c (fun z => J ξ (F.val0.eY z))
      (fun z => J η (F.val0.eY z)) = ⟪η, ξ⟫_ℂ

variable (D)

def WittExists : Prop := ∀ (X : HidaSetting D) (u : D.what₂.Word), ∃ wt, WittX X u wt

def GenusMatch (F : ∀ u, Formalism.L2.Forms.Forms0 D u) : Prop :=
  ∀ (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) ιA, WittX X u wt → IsAdeleIso X ιA →
    ∃ h0, LatMatchH X u (F u) wt ιA h0

def LevelConj (F : ∀ u, Formalism.L2.Forms.Forms0 D u) : Prop :=
  ∀ (X : HidaSetting D) (hK : X.LevelSubgroupCharacter) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) ιA h0, WittX X u wt → IsAdeleIso X ιA →
    LatMatchH X u (F u) wt ιA h0 →
    ∃ h0', LatMatchH X u (F u) wt ιA h0' ∧ LevelKH X u (F u) wt ιA h0' hK

def HcExists (F : ∀ u, Formalism.L2.Forms.Forms0 D u) : Prop :=
  ∀ (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) ιA h0, WittX X u wt → IsAdeleIso X ιA →
    ∀ c : (D.mem u).C.cls 0, ∃ h : Hfin X u,
      RepF X wt ιA (h : X.B.I.Gf) ((F u).cls0.y c * h0⁻¹)

def JExists (F : ∀ u, Formalism.L2.Forms.Forms0 D u) : Prop :=
  ∀ (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt →
    ∃ J : X.Vpi u →ₗ⋆[ℂ] (Formalism.L2.Forms.Fr D 0 (Nat.zero_le _) → ℂ), JOK X u (F u) wt J

def RescaleStep3 : Prop :=
  ∀ (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I), X.MeasTie hb →
    ∃ (mg : Formalism.L2.SG.Measures.MeasG X.B.I.cm.sig X.B.I.J D.R.rS) (hg : mg.IsTextNorm)
      (mw : ∀ u, Formalism.L2.SG.Measures.MeasW X.B.I.cm.sig X.B.I.J
        (⟨fun a => crdOf X.B.I X.ιE X.bas (X.eX a), fun a => crdOf X.B.I X.ιE X.bas (X.fY a),
          crdOf X.B.I X.ιE X.bas (X.zu u)⟩ : Formalism.L2.SG.Sub.Frame X.B.I.E X.B.I.n D.R.rS))
      (hw : ∀ u, (mw u).IsTextNorm),
      (Formalism.L2.SG.SettingExistsMeasured.withMeas X mg hg mw hw).MeasTie hb ∧
      ∃ ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ ∧
        Formalism.L2.SG.LocVol.IsStdChar ψ ∧
        Formalism.L2.SG.MassDataConc.MeasCompatψ (Formalism.L2.SG.SettingExistsMeasured.withMeas X mg hg mw hw) ψ ∧
        ∀ w, Formalism.L2.SG.LocVol.LocCompatX (Formalism.L2.SG.SettingExistsMeasured.withMeas X mg hg mw hw) ψ w

def WBlkExists : Prop :=
  Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (A : UnitaryGroupInstance D) (L : UnitaryLatticeData D) (P : AdditiveCharacterData A) (Rf : ReferenceFrame A L)
    (Bu : AutomorphicBundle A P Rf) (Pi : RepresentationData A L) (Mu : MuBlocks A L), Nonempty (WBlk A L Bu Pi Mu)

def ColDictCore : Prop :=
  ∀ (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F) (hK : X.LevelSubgroupCharacter),
    LevelMatch X Tr hK → Formalism.L2.SG.ColsDim.StabTriv (iotaF X u) (Ku X u hK) →
      ClsMatch X Tr hK ∧ ColDictInto X Tr hK ∧ ColDictBij X Tr hK ∧
      ∀ (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (cs : Formalism.L2.SG.TermOp.ColSys X u what₂)
        (hinj : Function.Injective (Formalism.L2.SG.TermOp.sharp hK cs)),
        Formalism.L2.SG.TermOp.ColReps hK cs → ColDictIsom X Tr hK cs hinj

end GlobalTheory.St

end
