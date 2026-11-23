import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ClassFrameCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.RowForm

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting MeasureTheory

open scoped Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace ClassFrameUnitaryProducts

variable {D : D7} (X : HidaSetting D)

theorem piU_mul_inv_apply (u : D.what₂.Word) {s : X.B.I.Ginf} (hs : s ∈ X.SinfU u) (y : X.Vpi u) :
    X.piU u s (X.piU u s⁻¹ y) = y := by
  have hm := (X.piU_rep u).2.1 s hs s⁻¹ (Formalism.L2.SG.RealObj.InfCut.sinfU_inv X u hs)
  rw [mul_inv_cancel, (X.piU_rep u).1] at hm
  show (X.piU u s * X.piU u s⁻¹) y = y
  rw [← hm]
  rfl

theorem frame_alg (u u' : D.what₂.Word) {h h' : X.B.I.Ginf} (hh : h ∈ X.SinfU u) (hh' : h' ∈ X.SinfU u')
    (O V : X.Vpi u' →L[ℂ] X.Vpi u) (c : ℂ)
    (hE : (X.piU u h⁻¹).comp (O.comp (X.piU u' h')) = c • V) :
    O = c • ((X.piU u h).comp (V.comp (X.piU u' h'⁻¹))) := by
  have h1 : O = (X.piU u h).comp (((X.piU u h⁻¹).comp (O.comp (X.piU u' h'))).comp (X.piU u' h'⁻¹)) := by
    ext x
    simp only [ContinuousLinearMap.comp_apply, piU_mul_inv_apply X u' hh', piU_mul_inv_apply X u hh]
  rw [h1, hE]
  ext x
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, map_smul]

theorem comp_smul_mid (u u' : D.what₂.Word) (h h' : X.B.I.Ginf) (O : X.Vpi u' →L[ℂ] X.Vpi u) (a : ℂ) :
    (X.piU u h⁻¹).comp ((a • O).comp (X.piU u' h')) = a • (X.piU u h⁻¹).comp (O.comp (X.piU u' h')) := by
  ext x
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, map_smul]

section Transfer

variable {n r k : ℕ}

def nrm1 (ε : Fin n → Bool) (f f' : Fin (r + 1) → Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) (wb : Fin k → Fin n → ℂ) :
    Fin k → ℂ :=
  (Formalism.L2.SG.RealObj.Dl (Formalism.L2.SG.RealObj.Zhat ε f f' g) (r + 1))⁻¹ •
    Formalism.L2.SG.RealObj.wCoord ε wb (Formalism.L2.SG.RealObj.xPr (Formalism.L2.SG.RealObj.Zhat ε f f' g) g f')

def nrm2 (ε : Fin n → Bool) (f f' : Fin (r + 1) → Fin n → ℂ) (g gi : Matrix (Fin n) (Fin n) ℂ)
    (wb' : Fin k → Fin n → ℂ) : Fin k → ℂ :=
  (star (Formalism.L2.SG.RealObj.Dl (Formalism.L2.SG.RealObj.Zhat ε f f' g) (r + 1)))⁻¹ •
    Formalism.L2.SG.RealObj.wCoord ε wb' (gi *ᵥ Formalism.L2.SG.RealObj.xUn (Formalism.L2.SG.RealObj.Zhat ε f f' g) f)

theorem isDFrame_transfer (ε : Fin n → Bool) (f f' : Fin (r + 1) → Fin n → ℂ) (g₁ gi₁ g₂ gi₂ : Matrix (Fin n) (Fin n) ℂ)
    (wb wb' : Fin k → Fin n → ℂ) (i0 i0' : Fin k) (h h' : Matrix (Fin k) (Fin k) ℂ)
    (hN1 : nrm1 ε f f' g₁ wb = nrm1 ε f f' g₂ wb) (hN2 : nrm2 ε f f' g₁ gi₁ wb' = nrm2 ε f f' g₂ gi₂ wb')
    (hU : ∀ y₂ : Fin n → ℂ, (∀ a, Formalism.L2.SG.HidaSetting.hJ ε (f a) y₂ = 0) →
      (∀ b, Formalism.L2.SG.HidaSetting.hJ ε (g₂ *ᵥ f' b) y₂ = 0) →
        ∃ y₁ : Fin n → ℂ, (∀ a, Formalism.L2.SG.HidaSetting.hJ ε (f a) y₁ = 0) ∧
          (∀ b, Formalism.L2.SG.HidaSetting.hJ ε (g₁ *ᵥ f' b) y₁ = 0) ∧
          Formalism.L2.SG.RealObj.wCoord ε wb y₁ = Formalism.L2.SG.RealObj.wCoord ε wb y₂ ∧
          Formalism.L2.SG.RealObj.wCoord ε wb' (gi₁ *ᵥ y₁) = Formalism.L2.SG.RealObj.wCoord ε wb' (gi₂ *ᵥ y₂))
    (hD : Formalism.L2.SG.RealObj.IsDFrame ε f f' g₁ gi₁ wb wb' i0 i0' h h') :
    Formalism.L2.SG.RealObj.IsDFrame ε f f' g₂ gi₂ wb wb' i0 i0' h h' := by
  obtain ⟨hu, hu', h1, h2, h3⟩ := hD
  refine ⟨hu, hu', ?_, ?_, fun y ha hb => ?_⟩
  · have e1 : nrm1 ε f f' g₁ wb = nrm1 ε f f' g₂ wb := hN1
    unfold nrm1 at e1
    rw [← e1]
    exact h1
  · have e2 : nrm2 ε f f' g₁ gi₁ wb' = nrm2 ε f f' g₂ gi₂ wb' := hN2
    unfold nrm2 at e2
    rw [← e2]
    exact h2
  · obtain ⟨y₁, ha1, hb1, hw1, hw⟩ := hU y ha hb
    rw [← hw, ← hw1]
    exact h3 y₁ ha1 hb1

end Transfer

end ClassFrameUnitaryProducts

variable {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
  (vR : Term D u u' (X.Fu u) (Y.what₂ u) → ℝ)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
  (κ : Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)

def dVal (h h' : X.B.I.Ginf) (s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) :
    X.Vpi u' →L[ℂ] X.Vpi u :=
  Formalism.L2.SG.PairVal.cTerm vR s.toTerm •
    ((X.piU u h).comp ((Formalism.L2.SG.RealObj.unscaledOperatorAtPointRepresentative X u u' 1 i0 i0' νq (Formalism.L2.SG.PairVal.ptOf s.toTerm)).comp
      (X.piU u' h'⁻¹)))

def PtValueC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s : LiftT X Y u u' κ R ρ), s.1.relevant →
    ∃ h h', Formalism.L2.SG.RealObj.IsDFrameX X u u' 1 i0 i0' s.1.pt.1 h h' ∧
      (X.piU u h⁻¹).comp ((chiOO X Y u u' s.1).comp (X.piU u' h')) =
        Formalism.L2.SG.PairVal.cTerm vR s.1.toTerm •
          Formalism.L2.SG.RealObj.unscaledOperatorAtPointRepresentative X u u' 1 i0 i0' νq (Formalism.L2.SG.PairVal.ptOf s.1.toTerm)

def VIndepLiftC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s : LiftT X Y u u' κ R ρ), s.1.relevant →
    ∀ h₁ h₁' h₂ h₂', Formalism.L2.SG.RealObj.IsDFrameX X u u' 1 i0 i0' s.1.pt.1 h₁ h₁' →
      Formalism.L2.SG.RealObj.IsDFrameX X u u' 1 i0 i0' s.1.pt.1 h₂ h₂' →
        (X.piU u h₁⁻¹).comp ((chiOO X Y u u' s.1).comp (X.piU u' h₁')) =
          (X.piU u h₂⁻¹).comp ((chiOO X Y u u' s.1).comp (X.piU u' h₂'))

def OOtNuC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s : LiftT X Y u u' κ R ρ), s.1.relevant →
    ∃ a : ℂ, Formalism.L2.SG.TermOp.OOt s.1 =
      a • (haveI := FiniteDimensional.complete ℂ (X.Vpi u)
        Formalism.L2.SG.TermOp.OO (νq s.1.pt.1) Set.univ (X.Wu u) (X.Wu u') s.1.pt.1)

def CommonDFrameC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ),
    ∃ h ∈ Formalism.L2.SG.RealObj.HsetU X u, ∃ h' ∈ Formalism.L2.SG.RealObj.HsetU X u', ∃ ζ : ℂ, ‖ζ‖ = 1 ∧
      ∀ s : LiftT X Y u u' κ R ρ, s.1.relevant →
        ∃ hs hs', Formalism.L2.SG.RealObj.IsDFrameX X u u' 1 i0 i0' s.1.pt.1 hs hs' ∧
          dVal X Y u u' vR i0 i0' νq hs hs' s.1 = ζ • dVal X Y u u' vR i0 i0' νq h h' s.1

def CommonDFrameExactC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ),
    ∃ h ∈ Formalism.L2.SG.RealObj.HsetU X u, ∃ h' ∈ Formalism.L2.SG.RealObj.HsetU X u',
      ∀ s : LiftT X Y u u' κ R ρ, s.1.relevant → Formalism.L2.SG.RealObj.IsDFrameX X u u' 1 i0 i0' s.1.pt.1 h h'

def IrrelZeroC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s : LiftT X Y u u' κ R ρ), ¬ s.1.relevant →
    chiOO X Y u u' s.1 = 0 ∧ (Formalism.L2.SG.PairVal.cTerm vR s.1.toTerm = 0 ∨
      Formalism.L2.SG.RealObj.unscaledOperatorAtPointRepresentative X u u' 1 i0 i0' νq (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) = 0)

def PairDFrameC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s₁ s₂ : LiftT X Y u u' κ R ρ),
    s₁.1.relevant → s₂.1.relevant → ∀ h h', Formalism.L2.SG.RealObj.IsDFrameX X u u' 1 i0 i0' s₁.1.pt.1 h h' →
      Formalism.L2.SG.RealObj.IsDFrameX X u u' 1 i0 i0' s₂.1.pt.1 h h'

def ScalarAgreeC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s₁ s₂ : LiftT X Y u u' κ R ρ),
    s₁.1.relevant → s₂.1.relevant → ∀ v,
      ClassFrameUnitaryProducts.nrm1 (X.B.I.ε v) (Formalism.L2.SG.RealObj.frm X u 1 v) (Formalism.L2.SG.RealObj.frm X u' 1 v)
          (uMat (s₁.1.pt.1 v)) (X.wfr u v) =
        ClassFrameUnitaryProducts.nrm1 (X.B.I.ε v) (Formalism.L2.SG.RealObj.frm X u 1 v) (Formalism.L2.SG.RealObj.frm X u' 1 v)
          (uMat (s₂.1.pt.1 v)) (X.wfr u v) ∧
      ClassFrameUnitaryProducts.nrm2 (X.B.I.ε v) (Formalism.L2.SG.RealObj.frm X u 1 v) (Formalism.L2.SG.RealObj.frm X u' 1 v)
          (uMat (s₁.1.pt.1 v)) (uMat ((s₁.1.pt.1 v)⁻¹)) (X.wfr u' v) =
        ClassFrameUnitaryProducts.nrm2 (X.B.I.ε v) (Formalism.L2.SG.RealObj.frm X u 1 v) (Formalism.L2.SG.RealObj.frm X u' 1 v)
          (uMat (s₂.1.pt.1 v)) (uMat ((s₂.1.pt.1 v)⁻¹)) (X.wfr u' v) ∧
      ∀ y₂ : Fin X.B.I.n → ℂ, (∀ a, Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (Formalism.L2.SG.RealObj.frm X u 1 v a) y₂ = 0) →
        (∀ b, Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (uMat (s₂.1.pt.1 v) *ᵥ Formalism.L2.SG.RealObj.frm X u' 1 v b) y₂ = 0) →
          ∃ y₁ : Fin X.B.I.n → ℂ, (∀ a, Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (Formalism.L2.SG.RealObj.frm X u 1 v a) y₁ = 0) ∧
            (∀ b, Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (uMat (s₁.1.pt.1 v) *ᵥ Formalism.L2.SG.RealObj.frm X u' 1 v b) y₁ = 0) ∧
            Formalism.L2.SG.RealObj.wCoord (X.B.I.ε v) (X.wfr u v) y₁ = Formalism.L2.SG.RealObj.wCoord (X.B.I.ε v) (X.wfr u v) y₂ ∧
            Formalism.L2.SG.RealObj.wCoord (X.B.I.ε v) (X.wfr u' v) (uMat ((s₁.1.pt.1 v)⁻¹) *ᵥ y₁) =
              Formalism.L2.SG.RealObj.wCoord (X.B.I.ε v) (X.wfr u' v) (uMat ((s₂.1.pt.1 v)⁻¹) *ᵥ y₂)

theorem pairDFrameC_of (hS : ScalarAgreeC X Y u u' κ) : PairDFrameC X Y u u' i0 i0' κ := by
  intro R ρ s₁ s₂ h₁ h₂ h h' hD
  refine ⟨hD.1, hD.2.1, fun v => ?_⟩
  obtain ⟨e1, e2, e3⟩ := hS R ρ s₁ s₂ h₁ h₂ v
  exact ClassFrameUnitaryProducts.isDFrame_transfer _ _ _ _ _ _ _ _ _ _ _ _ _ e1 e2 e3 (hD.2.2 v)

theorem classFrameOO1_one_mem (w : D.what₂.Word) : (1 : X.B.I.Ginf) ∈ Formalism.L2.SG.RealObj.HsetU X w := by
  intro v x _
  simp [uMat]

theorem commonDFrameExactC_of (hP : PtValueC X Y u u' vR i0 i0' νq κ) (hPair : PairDFrameC X Y u u' i0 i0' κ) :
    CommonDFrameExactC X Y u u' i0 i0' κ := by
  intro R ρ
  by_cases hex : ∃ s₀ : LiftT X Y u u' κ R ρ, s₀.1.relevant
  · obtain ⟨s₀, h₀⟩ := hex
    obtain ⟨h, h', hD, -⟩ := hP R ρ s₀ h₀
    exact ⟨h, hD.1, h', hD.2.1, fun s hs => hPair R ρ s₀ s h₀ hs h h' hD⟩
  · exact ⟨1, classFrameOO1_one_mem X u, 1, classFrameOO1_one_mem X u', fun s hs => absurd ⟨s, hs⟩ hex⟩

theorem commonDFrameC_of_exact (hE : CommonDFrameExactC X Y u u' i0 i0' κ) :
    CommonDFrameC X Y u u' vR i0 i0' νq κ := by
  intro R ρ
  obtain ⟨h, hh, h', hh', hs⟩ := hE R ρ
  exact ⟨h, hh, h', hh', 1, by simp, fun s hrel => ⟨h, h', hs s hrel, (one_smul ℂ _).symm⟩⟩

theorem vIndepLiftC_of (hF : OOtNuC X Y u u' νq κ) (hNu : Formalism.L2.SG.RealObj.NuQOK X u u' νq)
    (hVI : Formalism.L2.SG.RealObj.VIndep X u u' 1 i0 i0' νq) : VIndepLiftC X Y u u' i0 i0' κ := by
  intro R ρ s hrel h₁ h₁' h₂ h₂' hD₁ hD₂
  obtain ⟨a, ha⟩ := hF R ρ s hrel
  have hV := hVI hNu s.1.pt.1 h₁ h₁' h₂ h₂' hD₁ hD₂
  unfold chiOO
  rw [ha, smul_smul, ClassFrameUnitaryProducts.comp_smul_mid, ClassFrameUnitaryProducts.comp_smul_mid, hV]

theorem classFrameOO1_liftFrame (hP : PtValueC X Y u u' vR i0 i0' νq κ) (hVL : VIndepLiftC X Y u u' i0 i0' κ)
    (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s : LiftT X Y u u' κ R ρ) (hrel : s.1.relevant)
    (hs hs' : X.B.I.Ginf) (hD : Formalism.L2.SG.RealObj.IsDFrameX X u u' 1 i0 i0' s.1.pt.1 hs hs') :
    chiOO X Y u u' s.1 = dVal X Y u u' vR i0 i0' νq hs hs' s.1 := by
  obtain ⟨h0, h0', hD0, hEq⟩ := hP R ρ s hrel
  rw [hVL R ρ s hrel h0 h0' hs hs' hD0 hD] at hEq
  exact ClassFrameUnitaryProducts.frame_alg X u u' (Formalism.L2.SG.RealObj.InfCut.hsetU_sub X u hD.1)
    (Formalism.L2.SG.RealObj.InfCut.hsetU_sub X u' hD.2.1) _ _ _ hEq

theorem classFrameOO1_piIso_coe (w : D.what₂.Word) (g : X.B.I.Ginf) (hg : g ∈ X.SinfU w) :
    ((Formalism.L2.SG.RealObj.InfCut.piIso X w g hg : X.Vpi w ≃ₗᵢ[ℂ] X.Vpi w) : X.Vpi w →L[ℂ] X.Vpi w) = X.piU w g := by
  ext x
  rfl

theorem classFrameOO1_piIso_symm (w : D.what₂.Word) (g : X.B.I.Ginf) (hg : g ∈ X.SinfU w) :
    (((Formalism.L2.SG.RealObj.InfCut.piIso X w g hg).symm : X.Vpi w ≃ₗᵢ[ℂ] X.Vpi w) : X.Vpi w →L[ℂ] X.Vpi w) =
      X.piU w g⁻¹ := by
  rw [← Formalism.L2.SG.RealObj.InfCut.piIso_symm X w g hg]

theorem classFrameOO1_frameVal_piIso (h h' : X.B.I.Ginf) (hh : h ∈ X.SinfU u) (hh' : h' ∈ X.SinfU u')
    (s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) :
    frameVal X Y u u' vR i0 i0' νq (Formalism.L2.SG.RealObj.InfCut.piIso X u h hh)
      (Formalism.L2.SG.RealObj.InfCut.piIso X u' h' hh') s = dVal X Y u u' vR i0 i0' νq h h' s := by
  unfold frameVal dVal
  rw [classFrameOO1_piIso_coe, classFrameOO1_piIso_symm]

theorem commonFrameC_of (hP : PtValueC X Y u u' vR i0 i0' νq κ) (hVL : VIndepLiftC X Y u u' i0 i0' κ)
    (hCD : CommonDFrameC X Y u u' vR i0 i0' νq κ) (hZ : IrrelZeroC X Y u u' vR i0 i0' νq κ) :
    CommonFrameC X Y u u' vR i0 i0' νq κ := by
  intro R ρ
  obtain ⟨h, hh, h', hh', ζ, hζ, hcom⟩ := hCD R ρ
  have hS := Formalism.L2.SG.RealObj.InfCut.hsetU_sub X u hh
  have hS' := Formalism.L2.SG.RealObj.InfCut.hsetU_sub X u' hh'
  refine ⟨Formalism.L2.SG.RealObj.InfCut.piIso X u h hS, Formalism.L2.SG.RealObj.InfCut.piIso X u' h' hS', ζ, hζ,
    fun s A B hAB => ?_⟩
  rw [← hAB, classFrameOO1_frameVal_piIso]
  by_cases hrel : s.1.relevant
  · obtain ⟨hs, hs', hDs, hv⟩ := hcom s hrel
    rw [← hv]
    exact classFrameOO1_liftFrame X Y u u' vR i0 i0' νq κ hP hVL R ρ s hrel hs hs' hDs
  · obtain ⟨h0, hc⟩ := hZ R ρ s hrel
    rw [h0]
    unfold dVal
    rcases hc with hc | hc
    · rw [hc, zero_smul, smul_zero]
    · rw [hc]
      simp

theorem irrelZeroC_of (hV : LemmaVLiftC X Y u u' κ) (hAt : AtPtRelevantC X Y u u') :
    IrrelZeroC X Y u u' vR i0 i0' νq κ := by
  intro R ρ s hrel
  refine ⟨?_, Or.inl (cTerm_irrel X Y u u' vR hAt s.1.toTerm hrel)⟩
  unfold chiOO
  rw [hV R ρ s hrel, smul_zero]

theorem commonFrameC_of_vIndep (hP : PtValueC X Y u u' vR i0 i0' νq κ) (hF : OOtNuC X Y u u' νq κ)
    (hNu : Formalism.L2.SG.RealObj.NuQOK X u u' νq) (hVI : Formalism.L2.SG.RealObj.VIndep X u u' 1 i0 i0' νq)
    (hCD : CommonDFrameC X Y u u' vR i0 i0' νq κ) (hZ : IrrelZeroC X Y u u' vR i0 i0' νq κ) :
    CommonFrameC X Y u u' vR i0 i0' νq κ :=
  commonFrameC_of X Y u u' vR i0 i0' νq κ hP (vIndepLiftC_of X Y u u' i0 i0' νq κ hF hNu hVI) hCD hZ

theorem commonFrameC_of_cut (hP : PtValueC X Y u u' vR i0 i0' νq κ) (hF : OOtNuC X Y u u' νq κ)
    (hNu : Formalism.L2.SG.RealObj.NuQOK X u u' νq) (hVI : Formalism.L2.SG.RealObj.VIndep X u u' 1 i0 i0' νq)
    (hCD : CommonDFrameC X Y u u' vR i0 i0' νq κ) (hV : LemmaVLiftC X Y u u' κ) (hAt : AtPtRelevantC X Y u u') :
    CommonFrameC X Y u u' vR i0 i0' νq κ :=
  commonFrameC_of_vIndep X Y u u' vR i0 i0' νq κ hP hF hNu hVI hCD (irrelZeroC_of X Y u u' vR i0 i0' νq κ hV hAt)

theorem commonFrameC_of_pair (hP : PtValueC X Y u u' vR i0 i0' νq κ) (hF : OOtNuC X Y u u' νq κ)
    (hNu : Formalism.L2.SG.RealObj.NuQOK X u u' νq) (hVI : Formalism.L2.SG.RealObj.VIndep X u u' 1 i0 i0' νq)
    (hPair : PairDFrameC X Y u u' i0 i0' κ) (hV : LemmaVLiftC X Y u u' κ) (hAt : AtPtRelevantC X Y u u') :
    CommonFrameC X Y u u' vR i0 i0' νq κ :=
  commonFrameC_of_cut X Y u u' vR i0 i0' νq κ hP hF hNu hVI
    (commonDFrameC_of_exact X Y u u' vR i0 i0' νq κ (commonDFrameExactC_of X Y u u' vR i0 i0' νq κ hP hPair)) hV hAt

theorem commonFrameC_of_scalar (hP : PtValueC X Y u u' vR i0 i0' νq κ) (hF : OOtNuC X Y u u' νq κ)
    (hNu : Formalism.L2.SG.RealObj.NuQOK X u u' νq) (hVI : Formalism.L2.SG.RealObj.VIndep X u u' 1 i0 i0' νq)
    (hS : ScalarAgreeC X Y u u' κ) (hV : LemmaVLiftC X Y u u' κ) (hAt : AtPtRelevantC X Y u u') :
    CommonFrameC X Y u u' vR i0 i0' νq κ :=
  commonFrameC_of_pair X Y u u' vR i0 i0' νq κ hP hF hNu hVI (pairDFrameC_of X Y u u' i0 i0' κ hS) hV hAt

end Formalism.L2.SG.Pf.RowForm
