import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ColDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.WuDecay
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts

noncomputable section

open scoped InnerProductSpace
open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict Formalism.L2.SG.ProjRows

set_option linter.dupNamespace false

namespace Formalism.L2.SG.KerJoinS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section SSide

variable {D : D7} {X : HidaSetting D} {Y : Formalism.L2.SG.Full.Full X} (hF : FinX Y) (I : SIso D.s (sOf hF))

def colS (u : D.what₂.Word) (φ : D.what₂.Mu u) : ColT (hF.shInj u) :=
  I.eCu u ((D.s_Cu u).symm ⟨(D.eMu u φ).1, (D.eMu u φ).2.1⟩)

theorem besS_conc (u : D.what₂.Word) (φ : D.what₂.Mu u) (F : D.what₂.EE) :
    D.besS u φ F = ⟪I.eHH (D.sEE F), puC hF u (colS hF I u φ)⟫_ℂ := by
  show inner ℂ (D.sEE F) (D.s.Pu u ((D.s_Cu u).symm ⟨(D.eMu u φ).1, (D.eMu u φ).2.1⟩)) = _
  rw [← LinearIsometryEquiv.inner_map_map I.eHH, I.Pu_eq]
  rfl

end SSide

section Unfold

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter)

def perU (Fs : Set X.B.I.GA) (f : X.B.I.L2 X.B.μf X.B.fund) (T : Cu X u hK) : ℂ :=
  ∫ g in Fs, X.B.I.ext f g * Ph X u hK T g ∂(X.B.I.muA X.B.μf)

def BesselUnfold (Dt Fs : Set X.B.I.GA) : Prop :=
  IsReps X u Dt → InHH X u hK → IFinite X u hK → PhWellDef X u hK → PhProps X u hK →
    Formalism.L2.SG.WuDecay.FoldOK X u hK →
    IsFundamentalDomain (Srat X u) Fs (X.B.I.muA X.B.μf) →
    ∀ (f : X.B.I.L2 X.B.μf X.B.fund) (T : Cu X u hK),
      IntegrableOn (fun g => X.B.I.ext f g * Ph X u hK T g) Fs (X.B.I.muA X.B.μf) ∧
      ⟪star f, PuFun X u hK Dt T⟫_ℂ = perU X u hK Fs f T

def PoincareSeriesHypotheses (Dt Fs : Set X.B.I.GA) : Prop :=
  IsReps X u Dt ∧ InHH X u hK ∧ IFinite X u hK ∧ PhWellDef X u hK ∧ PhProps X u hK ∧
    Formalism.L2.SG.WuDecay.FoldOK X u hK ∧ IsFundamentalDomain (Srat X u) Fs (X.B.I.muA X.B.μf)

end Unfold

section Ker

variable {D : D7} (X : HidaSetting D) (G : GoodOp X) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G)
  {Fm : ∀ u, Formalism.L2.Forms.Forms0 D u} (Tr : ∀ u, Transport X u (Fm u)) (hK : X.LevelSubgroupCharacter)

def rowL (F : D.what₂.EE) : X.B.I.L2 X.B.μf X.B.fund := ((j F : EEC X G) : L2X X)

def KerSide (Fs : D.what₂.Word → Set X.B.I.GA) : Prop :=
  ∃ V : D.what₂.EE ≃ₗᵢ[ℂ] D.what₂.EE, ∀ u, ∃ a : ℂ, a ≠ 0 ∧ ∃ U : D.what₂.Mu u ≃ₗᵢ[ℂ] D.what₂.Mu u,
    ∀ (φ : D.what₂.Mu u) (F : D.what₂.Amb D.what₂.mu0), F ∈ D.what₂.V0 D.what₂.mu0 →
    ∀ T : Cu X u hK, colDictL X (Tr u) hK T =
        ((D.eMu u (U φ) : (D.mem u).A.Mram) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) →
      D.what₂.perCol u D.what₂.mu0 φ F = a * perU X u hK (Fs u) (rowL X G j (V (D.what₂.iota D.what₂.mu0 F))) T

def KerJoinS (Dt : D.what₂.Word → Set X.B.I.GA) : Prop :=
  ∃ V : D.what₂.EE ≃ₗᵢ[ℂ] D.what₂.EE, ∀ u, ∃ a : ℂ, a ≠ 0 ∧ ∃ U : D.what₂.Mu u ≃ₗᵢ[ℂ] D.what₂.Mu u,
    ∀ (φ : D.what₂.Mu u) (F : D.what₂.Amb D.what₂.mu0), F ∈ D.what₂.V0 D.what₂.mu0 →
    ∀ T : Cu X u hK, colDictL X (Tr u) hK T =
        ((D.eMu u (U φ) : (D.mem u).A.Mram) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) →
      D.what₂.perCol u D.what₂.mu0 φ F =
        a * ⟪((conjHH X G (j (V (D.what₂.iota D.what₂.mu0 F))) : HHX X) : L2X X), PuFun X u hK (Dt u) T⟫_ℂ

theorem kerJoinS_of_parts (Dt Fs : D.what₂.Word → Set X.B.I.GA) (hH : ∀ u, PoincareSeriesHypotheses X u hK (Dt u) (Fs u))
    (hU : ∀ u, BesselUnfold X u hK (Dt u) (Fs u)) (hS : KerSide X G j Tr hK Fs) : KerJoinS X G j Tr hK Dt := by
  obtain ⟨V, hV⟩ := hS
  refine ⟨V, fun u => ?_⟩
  obtain ⟨a, ha, U, hU'⟩ := hV u
  refine ⟨a, ha, U, fun φ F hF T hT => ?_⟩
  rw [hU' φ F hF T hT]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hH u
  have e := (hU u h1 h2 h3 h4 h5 h6 h7 (rowL X G j (V (D.what₂.iota D.what₂.mu0 F))) T).2
  rw [← e, conjHH_apply]
  rfl

end Ker

theorem exists_Q_iota {D : D7} (hon : (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤) (x : D.what₂.EE) :
    ∃ q ∈ D.what₂.Qsp D.what₂.mu0, D.what₂.iota D.what₂.mu0 q = x := by
  have hx : x ∈ (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) := by
    rw [hon]; exact Submodule.mem_top
  obtain ⟨p, hp, rfl⟩ := hx
  have hU : (D.what₂.Usp D.what₂.mu0).starProjection p ∈ D.what₂.Usp D.what₂.mu0 :=
    (D.what₂.Usp D.what₂.mu0).starProjection_apply_mem p
  have hU1 : (D.what₂.Usp D.what₂.mu0).starProjection p ∈ D.what₂.V0 D.what₂.mu0 := (Submodule.mem_inf.mp hU).1
  have hU2 : D.what₂.iota D.what₂.mu0 ((D.what₂.Usp D.what₂.mu0).starProjection p) = 0 :=
    LinearMap.mem_ker.mp (Submodule.mem_inf.mp hU).2
  refine ⟨p - (D.what₂.Usp D.what₂.mu0).starProjection p, ?_, ?_⟩
  · show _ ∈ D.what₂.V0 D.what₂.mu0 ⊓ (D.what₂.Usp D.what₂.mu0)ᗮ
    exact Submodule.mem_inf.mpr ⟨Submodule.sub_mem _ hp hU1,
      (D.what₂.Usp D.what₂.mu0).sub_starProjection_mem_orthogonal p⟩
  · rw [map_sub, hU2, sub_zero]

section Bessel

variable {D : D7} {X : HidaSetting D} {Y : Formalism.L2.SG.Full.Full X} (hF : FinX Y) (I : SIso D.s (sOf hF))
  {Fm : ∀ u, Formalism.L2.Forms.Forms0 D u} (Tr : ∀ u, Transport X u (Fm u))

def ColJoinS : Prop :=
  ∀ u, ∃ W : D.what₂.Mu u ≃ₗᵢ[ℂ] D.what₂.Mu u, ∀ ψ : D.what₂.Mu u,
    colDictL X (Tr u) Y.hK (colS hF I u (W ψ) : Cu X u Y.hK) =
      ((D.eMu u ψ : (D.mem u).A.Mram) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ)

theorem colJoinS_of_pin (hIn : ∀ u, ColDictInto X (Tr u) Y.hK) (hBi : ∀ u, ColDictBij X (Tr u) Y.hK)
    (hpin : ∀ u (x : D.s.Cu u),
      (I.eCu u x : Cu X u Y.hK) = (colDict X (Tr u) Y.hK (hIn u) (hBi u)).symm (D.s_Cu u x)) :
    ColJoinS hF I Tr := by
  intro u
  refine ⟨LinearIsometryEquiv.refl ℂ _, fun ψ => ?_⟩
  have e1 := (colDict X (Tr u) Y.hK (hIn u) (hBi u)).apply_symm_apply
      ((D.s_Cu u) ((D.s_Cu u).symm ⟨(D.eMu u ψ).1, (D.eMu u ψ).2.1⟩))
  rw [(D.s_Cu u).apply_symm_apply] at e1
  have e2 := congrArg Subtype.val e1
  change colDictL X (Tr u) Y.hK
    ((I.eCu u ((D.s_Cu u).symm ⟨(D.eMu u ψ).1, (D.eMu u ψ).2.1⟩) : Cu X u Y.hK)) = _
  rw [hpin, (D.s_Cu u).apply_symm_apply]
  exact e2

theorem besselId_of_joins (G : GoodOp X) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G)
    (hRow : ∀ F, I.eHH (D.sEE F) = conjHH X G (j F)) (hCol : ColJoinS hF I Tr)
    (hK : KerJoinS X G j Tr Y.hK Y.Dt) (hB : Formalism.BasicNotions.Rows.BuDefQ D.what₂)
    (hon : (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤) : Formalism.MainNotions.LocalQuadraticParts.adm13 D := by
  obtain ⟨V, hK⟩ := hK
  refine ⟨V, fun u => ?_⟩
  obtain ⟨a, ha, U, hk⟩ := hK u
  obtain ⟨W, hW⟩ := hCol u
  refine ⟨a, ha, U.trans W, fun φ x => ?_⟩
  obtain ⟨q, hq, rfl⟩ := exists_Q_iota hon x
  rw [hB u φ, D.what₂.sec_iota _ q hq, hk φ q hq.1 (colS hF I u (W (U φ))) (hW (U φ)),
    LinearIsometryEquiv.trans_apply, besS_conc hF I, hRow]
  rfl

end Bessel

end Formalism.L2.SG.KerJoinS
