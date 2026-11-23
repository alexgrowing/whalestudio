import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.SettingExistsMeasured
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Formalism.SatakeDualWeyl.StatementC
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf

noncomputable section

open scoped TensorProduct
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting

set_option linter.dupNamespace false

namespace Formalism.L2.SG.SettingExistsAdapted

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def toHostF (X : HidaSetting D) (a : X.B.I.F) : D.host.F :=
  ⟨X.ιE (algebraMap X.B.I.F X.B.I.E a), (X.ιE_F _).2 ⟨a, rfl⟩⟩

def SplitPin (X : HidaSetting D) : Prop :=
  ∀ (p : HeightOneSpectrum (𝓞 D.host.F))
    (sp : Formalism.MainNotions.S.Loc.SplitAt (D.s.atP p).Fp (D.s.atP p).Ep (D.s.atP p).cj (Formalism.MainNotions.S.Loc.resChar p)),
    (D.s.atP p).split = some sp →
    ∃ (v : HeightOneSpectrum (𝓞 X.B.I.F)) (φ : v.adicCompletion X.B.I.F ≃+* (D.s.atP p).Fp)
      (c : X.B.I.E ⊗[X.B.I.F] v.adicCompletion X.B.I.F →+* (D.s.atP p).Ep),
      Continuous φ ∧
      (∀ a : X.B.I.F, φ (algebraMap X.B.I.F (v.adicCompletion X.B.I.F) a) = (D.s.atP p).ιF (toHostF X a)) ∧
      (∀ x : X.B.I.E, c (x ⊗ₜ[X.B.I.F] (1 : v.adicCompletion X.B.I.F)) = (D.s.atP p).ιE (X.ιE x)) ∧
      (∀ a : v.adicCompletion X.B.I.F,
        c ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] a) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (φ a)) ∧
      sp.e (c (Formalism.UG.prV (E := X.B.I.E) v X.ew)) = (1, 0)

variable (D)

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

def TransportExists3 (F : ∀ u, Formalism.L2.Forms.Forms0 D u) : Prop :=
  Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∃ X : HidaSetting D, ∃ hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I,
    X.MeasTie hb ∧ Formalism.L2.SG.WuDecay.WuDecay X ∧
    Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) ∧
    ∃ hK : X.LevelSubgroupCharacter, ∀ u, ∃ Tr : Formalism.L2.SG.ColDict.Transport X u (F u), Formalism.L2.SG.ColDict.LevelMatch X Tr hK

def SettingExistsAdapted (F : ∀ u, Formalism.L2.Forms.Forms0 D u) : Prop :=
  Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∃ X : HidaSetting D, ∃ hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I,
    ∃ ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ,
    X.MeasTie hb ∧ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ ∧ Formalism.L2.SG.LocVol.IsStdChar ψ ∧
    Formalism.L2.SG.MassDataConc.MeasCompatψ X ψ ∧ (∀ w, Formalism.L2.SG.LocVol.LocCompatX X ψ w) ∧
    Formalism.L2.SG.WuDecay.WuDecay X ∧ Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) ∧
    (∃ θ : ℝ, ∃ C : Formalism.L2.SG.LocWSOf.Choice X θ, Formalism.L2.SG.LocWSOf.WuBessel C) ∧
    ∃ hK : X.LevelSubgroupCharacter, ∀ u, ∃ Tr : Formalism.L2.SG.ColDict.Transport X u (F u), Formalism.L2.SG.ColDict.LevelMatch X Tr hK

def WuBesselStep : Prop :=
  Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ X : HidaSetting D, ∃ θ : ℝ, ∃ C : Formalism.L2.SG.LocWSOf.Choice X θ, Formalism.L2.SG.LocWSOf.WuBessel C

end Formalism.L2.SG.SettingExistsAdapted

namespace Formalism.L2.SG.SettingExistsAdapted

open Formalism.MainNotions.S Formalism.L2.SG.SplitPrimeNormLemmas Formalism.L2.SG.ColDict Matrix
open scoped InnerProductSpace

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

def RefExistsS : Prop :=
  ∀ (A : UnitaryGroupInstance D) (L : UnitaryLatticeData D), ∃ Rf : ReferenceFrame A L, ∀ (P : AdditiveCharacterData A) (Xu : TransportData A L Rf) (Bu : AutomorphicBundle A P Rf)
    (Pi : RepresentationData A L) (Mu : MuBlocks A L) (Wb : WBlk A L Bu Pi Mu) (Mb : MBlk A L), SplitPin (mk A L P Rf Xu Bu Pi Mu Wb Mb)

def WittExists : Prop := ∀ (X : HidaSetting D) (u : D.what₂.Word), ∃ wt, WittX X u wt

def AdeleIsoExists : Prop := ∀ X : HidaSetting D, ∃ ιA, IsAdeleIso X ιA

def GenusMatch (F : ∀ u, Formalism.L2.Forms.Forms0 D u) : Prop :=
  ∀ (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) ιA, WittX X u wt → IsAdeleIso X ιA →
    ∃ h0, LatMatchH X u (F u) wt ιA h0

def LevelConj (F : ∀ u, Formalism.L2.Forms.Forms0 D u) : Prop :=
  ∀ (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) ιA h0, WittX X u wt → IsAdeleIso X ιA →
    LatMatchH X u (F u) wt ιA h0 →
    ∃ h0', LatMatchH X u (F u) wt ιA h0' ∧ LevelKH X u (F u) wt ιA h0' (Formalism.L2.SG.Closed.level_subgroup_is_group X)

def HcExists (F : ∀ u, Formalism.L2.Forms.Forms0 D u) : Prop :=
  ∀ (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) ιA h0, WittX X u wt → IsAdeleIso X ιA →
    ∀ c : (D.mem u).C.cls 0, ∃ h : Hfin X u,
      RepF X wt ιA (h : X.B.I.Gf) ((F u).cls0.y c * h0⁻¹)

def JExists (F : ∀ u, Formalism.L2.Forms.Forms0 D u) : Prop :=
  ∀ (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt →
    ∃ J : X.Vpi u →ₗ⋆[ℂ] (Formalism.L2.Forms.Fr D 0 (Nat.zero_le _) → ℂ), JOK X u (F u) wt J

theorem transport_of (F : ∀ u, Formalism.L2.Forms.Forms0 D u) (h1 : WittExists D) (h2 : AdeleIsoExists D)
    (h0g : GenusMatch D F) (h3 : LevelConj D F) (h4 : HcExists D F) (h5 : JExists D F) (X : HidaSetting D)
    (u : D.what₂.Word) :
    ∃ Tr : Transport X u (F u), LevelMatch X Tr (Formalism.L2.SG.Closed.level_subgroup_is_group X) := by
  obtain ⟨wt, hw⟩ := h1 X u
  obtain ⟨ιA, hι⟩ := h2 X
  obtain ⟨g0, hg0⟩ := h0g X u wt ιA hw hι
  obtain ⟨h0, hL, hK⟩ := h3 X u wt ιA g0 hw hι hg0
  choose hcf hcr using h4 X u wt ιA h0 hw hι
  obtain ⟨J, hJ1, hJ2, hJ3⟩ := h5 X u wt hw
  exact ⟨⟨wt, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2, ιA, hι.1, hι.2, h0, hcf, hcr, J, hJ1, hJ2, hJ3⟩, hL, hK⟩

end Formalism.L2.SG.SettingExistsAdapted
