import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.ClassFrame

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.RowForm

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.MassDataForm MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (Y : Formalism.L2.SG.Full.Full X)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
  (vR : Term D u u' (X.Fu u) (Y.what₂ u) → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' (X.Fu u) (Y.what₂ u))
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
  (κ : Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)

def chiOO (s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) : X.Vpi u' →L[ℂ] X.Vpi u :=
  Formalism.L2.SG.TermOp.chiN X (Formalism.L2.SG.TermOp.kOf X u u' ((Y.cs u).h ((Y.cs u).base s.lam) : X.B.I.Gf)
            ((Y.cs u').h ((Y.cs u').base s.lam') : X.B.I.Gf) s.pt) • Formalism.L2.SG.TermOp.OOt s

def OOnu (s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) : X.Vpi u' →L[ℂ] X.Vpi u :=
  haveI := FiniteDimensional.complete ℂ (X.Vpi u)
  Formalism.L2.SG.TermOp.OO (νq s.pt.1) Set.univ (X.Wu u) (X.Wu u') s.pt.1

def frameVal (A : X.Vpi u ≃ₗᵢ[ℂ] X.Vpi u) (B : X.Vpi u' ≃ₗᵢ[ℂ] X.Vpi u')
    (s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) : X.Vpi u' →L[ℂ] X.Vpi u :=
  Formalism.L2.SG.PairVal.cTerm vR s.toTerm •
    ((A : X.Vpi u →L[ℂ] X.Vpi u).comp
      ((Formalism.L2.SG.RealObj.unscaledOperatorAtPointRepresentative X u u' 1 i0 i0' νq (Formalism.L2.SG.PairVal.ptOf s.toTerm)).comp (B.symm : X.Vpi u' →L[ℂ] X.Vpi u')))

def FormAllVolC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s : LiftT X Y u u' κ R ρ), s.1.relevant →
    Formalism.L2.SG.TermOp.OOt s.1 = ((vR s.1.toTerm : ℝ) : ℂ) • OOnu X Y u u' νq s.1

def NormalFormC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s : LiftT X Y u u' κ R ρ), s.1.relevant →
    ∃ (A : X.Vpi u ≃ₗᵢ[ℂ] X.Vpi u) (B : X.Vpi u' ≃ₗᵢ[ℂ] X.Vpi u'),
      chiOO X Y u u' s.1 = frameVal X Y u u' vR i0 i0' νq A B s.1

def CommonFrameC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ),
    ∃ (U : X.Vpi u ≃ₗᵢ[ℂ] X.Vpi u) (U' : X.Vpi u' ≃ₗᵢ[ℂ] X.Vpi u') (ζ : ℂ), ‖ζ‖ = 1 ∧
      ∀ (s : LiftT X Y u u' κ R ρ) (A : X.Vpi u ≃ₗᵢ[ℂ] X.Vpi u) (B : X.Vpi u' ≃ₗᵢ[ℂ] X.Vpi u'),
        chiOO X Y u u' s.1 = frameVal X Y u u' vR i0 i0' νq A B s.1 →
          frameVal X Y u u' vR i0 i0' νq A B s.1 = ζ • frameVal X Y u u' vR i0 i0' νq U U' s.1

def LemmaVLiftC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s : LiftT X Y u u' κ R ρ), ¬ s.1.relevant →
    Formalism.L2.SG.TermOp.OOt s.1 = 0

def AtPtRelevantC : Prop :=
  ∀ (t : Term D u u' (X.Fu u) (Y.what₂ u)) (w : Point D.host.E (D.R.rS + 1)), t.atPt w → t.relevant

theorem cTerm_irrel (hAt : AtPtRelevantC X Y u u') (t : Term D u u' (X.Fu u) (Y.what₂ u)) (ht : ¬ t.relevant) :
    Formalism.L2.SG.PairVal.cTerm vR t = 0 := by
  unfold Formalism.L2.SG.PairVal.cTerm
  rw [dif_neg]
  rintro ⟨w, hw⟩
  exact ht (hAt t w hw)

end Formalism.L2.SG.Pf.RowForm

namespace Formalism.L2.SG.Pf

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.Pf.RowForm
  MeasureTheory

theorem classFrameOO_of {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
    (vR : Term D u u' (X.Fu u) (Y.what₂ u) → ℝ)
    (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (κ : Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)
    (hB : NormalFormC X Y u u' vR i0 i0' νq κ)
    (hC : CommonFrameC X Y u u' vR i0 i0' νq κ) (hV : LemmaVLiftC X Y u u' κ) (hAt : AtPtRelevantC X Y u u') :
    ClassFrameOO X Y u u' vR i0 i0' νq κ := by
  intro R ρ
  obtain ⟨U, U', ζ, hζ, hU⟩ := hC R ρ
  refine ⟨U, U', ζ, hζ, fun s => ?_⟩
  by_cases hs : s.1.relevant
  · obtain ⟨A, B, hAB⟩ := hB R ρ s hs
    have h1 := hAB.trans (hU s A B hAB)
    unfold chiOO frameVal at h1
    rw [h1, smul_smul]
  · rw [hV R ρ s hs, smul_zero, cTerm_irrel X Y u u' vR hAt _ hs, mul_zero, zero_smul]

end Formalism.L2.SG.Pf
