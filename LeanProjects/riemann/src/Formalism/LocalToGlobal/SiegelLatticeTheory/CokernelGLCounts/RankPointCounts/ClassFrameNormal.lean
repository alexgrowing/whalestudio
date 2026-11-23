import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ClassFrameCut

noncomputable section

open scoped Classical ComplexConjugate

namespace Formalism.L2.SG.Pf.RowForm

namespace ClassFrameNormal

open MeasureTheory

section Gen

variable {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V']

theorem oo_map_mulLeft {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G)
    [CompleteSpace V] (Ph : G → V) (Ph' : G → V') (γ s s' : G) (a b : ℂ)
    (A : V ≃ₗᵢ[ℂ] V) (B : V' ≃ₗᵢ[ℂ] V') (hA : ∀ x, Ph (s * x) = a • A (Ph x))
    (hB : ∀ x, Ph' (s' * x) = b • B (Ph' x)) :
    Formalism.L2.SG.TermOp.OO (μ.map (fun x => s * x)) Set.univ Ph Ph' (s * γ * s'⁻¹) =
      (a * conj b) • ((A.toContinuousLinearEquiv : V →L[ℂ] V).comp
        ((Formalism.L2.SG.TermOp.OO μ Set.univ Ph Ph' γ).comp (B.symm.toContinuousLinearEquiv : V' →L[ℂ] V'))) := by
  classical
  have hEF : ∀ F : V' →L[ℂ] V,
      (B.toContinuousLinearEquiv.arrowCongr A.toContinuousLinearEquiv) F =
        (A.toContinuousLinearEquiv : V →L[ℂ] V).comp
          (F.comp (B.symm.toContinuousLinearEquiv : V' →L[ℂ] V')) := by
    intro F
    ext ξ
    simp [ContinuousLinearEquiv.arrowCongr_apply]
  have hmap : ∀ f : G → (V' →L[ℂ] V),
      ∫ x, f x ∂(μ.map fun x => s * x) = ∫ x, f (s * x) ∂μ :=
    fun f => (MeasurableEquiv.mulLeft s).measurableEmbedding.integral_map f
  have hpt : ∀ x, Formalism.L2.SG.TermOp.rk1 (Ph (s * x)) (Ph' ((s * γ * s'⁻¹)⁻¹ * (s * x))) =
      (a * conj b) • (B.toContinuousLinearEquiv.arrowCongr A.toContinuousLinearEquiv)
        (Formalism.L2.SG.TermOp.rk1 (Ph x) (Ph' (γ⁻¹ * x))) := by
    intro x
    have h1 : (s * γ * s'⁻¹)⁻¹ * (s * x) = s' * (γ⁻¹ * x) := by group
    rw [h1, hA, hB, hEF, Formalism.L2.SG.RealObj.InfCut.rank_one_smul_isometry]
  unfold Formalism.L2.SG.TermOp.OO
  rw [Measure.restrict_univ, Measure.restrict_univ, hmap]
  simp_rw [hpt]
  rw [integral_smul, ContinuousLinearEquiv.integral_comp_comm, hEF]

end Gen

end ClassFrameNormal

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.MassDataForm MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
  (vR : Term D u u' (X.Fu u) (Y.what₂ u) → ℝ)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
  (κ : Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)

def LiftAtSomeC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s : LiftT X Y u u' κ R ρ), s.1.relevant →
    ∃ w, s.1.toTerm.atPt w

def LiftDecompC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s : LiftT X Y u u' κ R ρ), s.1.relevant →
    (∃ γ, Formalism.L2.SG.RealObj.IsPtRep X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) γ) ∧
      ∃ g ∈ X.SinfU u, ∃ g' ∈ X.SinfU u',
        s.1.pt.1 = g * Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) * g'⁻¹

def DFrameAtS (sc : ℝ) : Prop :=
  0 < sc → ∀ w : Point D.host.E (D.R.rS + 1), (∃ γ, Formalism.L2.SG.RealObj.IsPtRep X u u' w γ) →
    (∀ v, 0 < Formalism.L2.SG.RealObj.GX X u u' D.host.rdE (Formalism.L2.SG.RealObj.gamW X u u' w) v) →
      ∃ h h', Formalism.L2.SG.RealObj.IsDFrameX X u u' sc i0 i0' (Formalism.L2.SG.RealObj.gamW X u u' w) h h'

def LiftGPosC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s : LiftT X Y u u' κ R ρ), s.1.relevant →
    ∀ v, 0 < Formalism.L2.SG.RealObj.GX X u u' D.host.rdE
      (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm)) v

def FormTranspC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s : LiftT X Y u u' κ R ρ), s.1.relevant →
    ∀ g ∈ X.SinfU u, ∀ g' ∈ X.SinfU u',
      s.1.pt.1 = g * Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) * g'⁻¹ →
      Formalism.L2.SG.TermOp.OOt s.1 = ((vR s.1.toTerm : ℝ) : ℂ) •
        (haveI := FiniteDimensional.complete ℂ (X.Vpi u)
         Formalism.L2.SG.TermOp.OO
          ((νq (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm))).map (fun x => g * x))
          Set.univ (X.Wu u) (X.Wu u') s.1.pt.1)

def PhaseTieC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s : LiftT X Y u u' κ R ρ), s.1.relevant →
    ∀ g ∈ X.SinfU u, ∀ g' ∈ X.SinfU u',
      s.1.pt.1 = g * Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) * g'⁻¹ →
      Formalism.L2.SG.TermOp.chiN X (Formalism.L2.SG.TermOp.kOf X u u' ((Y.cs u).h ((Y.cs u).base s.1.lam) : X.B.I.Gf)
                ((Y.cs u').h ((Y.cs u').base s.1.lam') : X.B.I.Gf) s.1.pt) *
        (X.psiInfU u g * conj (X.psiInfU u' g')) =
        Formalism.L2.SG.PairVal.phaseAt s.1.toTerm (Formalism.L2.SG.PairVal.ptOf s.1.toTerm)

theorem normalFormC_of (h1 : LiftAtSomeC X Y u u' κ)
    (h2 : Formalism.L2.SG.PairVal.CellPtUnique D u u' (X.Fu u) (Y.what₂ u))
    (h3 : LiftDecompC X Y u u' κ) (h4 : DFrameAtS X u u' i0 i0' 1) (h4' : LiftGPosC X Y u u' κ)
    (h5 : FormTranspC X Y u u' vR νq κ) (h6 : PhaseTieC X Y u u' κ) :
    NormalFormC X Y u u' vR i0 i0' νq κ := by
  classical
  haveI := FiniteDimensional.complete ℂ (X.Vpi u)
  haveI := FiniteDimensional.complete ℂ (X.Vpi u')
  intro R ρ s hs
  obtain ⟨⟨γ0, hγ0⟩, g, hg, g', hg', hpt⟩ := h3 R ρ s hs
  obtain ⟨w0, hw0⟩ := h1 R ρ s hs
  have hex : ∃ w, s.1.toTerm.atPt w ∧ s.1.toTerm.relevant := ⟨w0, hw0, hs⟩
  have hptOf : Formalism.L2.SG.PairVal.ptOf s.1.toTerm = w0 := by
    have e : Formalism.L2.SG.PairVal.ptOf s.1.toTerm = hex.choose := by
      unfold Formalism.L2.SG.PairVal.ptOf
      rw [dif_pos hex]
    rw [e]
    exact h2 _ _ _ hex.choose_spec.1 hw0
  have hex1 : ∃ w, s.1.toTerm.atPt w := ⟨w0, hw0⟩
  have hc : Formalism.L2.SG.PairVal.cTerm vR s.1.toTerm =
      Formalism.L2.SG.PairVal.phaseAt s.1.toTerm (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) * (vR s.1.toTerm : ℂ) := by
    unfold Formalism.L2.SG.PairVal.cTerm
    rw [dif_pos hex1]
    unfold Formalism.L2.SG.PairVal.cAt
    rw [hptOf, h2 _ _ _ hex1.choose_spec hw0]
  have hexF : ∃ p : X.B.I.Ginf × X.B.I.Ginf, Formalism.L2.SG.RealObj.IsDFrameX X u u' 1 i0 i0'
      (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm)) p.1 p.2 := by
    obtain ⟨h, h', hh⟩ := h4 one_pos _ ⟨γ0, hγ0⟩ (h4' R ρ s hs)
    exact ⟨(h, h'), hh⟩
  have hS := Formalism.L2.SG.RealObj.InfCut.hsetU_sub X u hexF.choose_spec.1
  have hS' := Formalism.L2.SG.RealObj.InfCut.hsetU_sub X u' hexF.choose_spec.2.1
  have hV : Formalism.L2.SG.RealObj.unscaledOperatorAtPointRepresentative X u u' 1 i0 i0' νq (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) =
      ((Formalism.L2.SG.RealObj.InfCut.piIso X u hexF.choose.1 hS).symm.toContinuousLinearEquiv :
          X.Vpi u →L[ℂ] X.Vpi u).comp
        ((Formalism.L2.SG.TermOp.OO (νq (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm)))
          Set.univ (X.Wu u) (X.Wu u')
          (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm))).comp
          ((Formalism.L2.SG.RealObj.InfCut.piIso X u' hexF.choose.2 hS').toContinuousLinearEquiv :
            X.Vpi u' →L[ℂ] X.Vpi u')) := by
    rw [Formalism.L2.SG.RealObj.InfCut.piIso_symm, Formalism.L2.SG.RealObj.InfCut.piIso_coe]
    unfold Formalism.L2.SG.RealObj.unscaledOperatorAtPointRepresentative
    rw [if_pos ⟨γ0, hγ0⟩]
    unfold Formalism.L2.SG.RealObj.unscaledFrameConjugatedOperator
    rw [dif_pos hexF]
  refine ⟨(Formalism.L2.SG.RealObj.InfCut.piIso X u hexF.choose.1 hS).trans
      (Formalism.L2.SG.RealObj.InfCut.piIso X u g hg),
    (Formalism.L2.SG.RealObj.InfCut.piIso X u' hexF.choose.2 hS').trans
      (Formalism.L2.SG.RealObj.InfCut.piIso X u' g' hg'), ?_⟩
  have hA : ∀ x, X.Wu u (g * x) =
      X.psiInfU u g • Formalism.L2.SG.RealObj.InfCut.piIso X u g hg (X.Wu u x) := by
    intro x
    rw [Formalism.L2.SG.RealObj.InfCut.piIso_apply]
    exact (X.Wu_spec u).1 g hg x
  have hB : ∀ x, X.Wu u' (g' * x) =
      X.psiInfU u' g' • Formalism.L2.SG.RealObj.InfCut.piIso X u' g' hg' (X.Wu u' x) := by
    intro x
    rw [Formalism.L2.SG.RealObj.InfCut.piIso_apply]
    exact (X.Wu_spec u').1 g' hg' x
  have hO := ClassFrameNormal.oo_map_mulLeft
    (νq (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm)))
    (X.Wu u) (X.Wu u') (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm)) g g'
    (X.psiInfU u g) (X.psiInfU u' g') _ _ hA hB
  have hph := h6 R ρ s hs g hg g' hg' hpt
  unfold chiOO frameVal
  rw [h5 R ρ s hs g hg g' hg' hpt, hc, hV, hpt, hO, ← hph]
  ext ξ
  simp [smul_smul, LinearIsometryEquiv.trans_apply]
  try ring_nf

end Formalism.L2.SG.Pf.RowForm
