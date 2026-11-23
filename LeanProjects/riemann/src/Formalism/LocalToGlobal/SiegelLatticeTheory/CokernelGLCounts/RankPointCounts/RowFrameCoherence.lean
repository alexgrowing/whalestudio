import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataForm

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
  (κ : Term D u u' (X.Fu u) (Y.what₂ u) → ℕ) (nc : ℝ)

abbrev ClassT (ρ : ℕ) : Type := {t : Term D u u' (X.Fu u) (Y.what₂ u) // Formalism.L2.SG.DataInst.Elig t ∧ κ t = ρ}

def clsVec (ρ : ℕ) : Formalism.L2.SG.PackageTie.HS (X.Vpi u') (X.Vpi u) :=
  ∑' t : ClassT X Y u u' κ ρ,
    (((Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u) t.1.lam) : ℝ) : ℂ) * Formalism.L2.SG.PairVal.cTerm vR t.1) •
      Formalism.L2.SG.PackageTie.hsEmb (Formalism.L2.SG.RealObj.unscaledOperatorAtPointRepresentative X u u' 1 i0 i0' νq (Formalism.L2.SG.PairVal.ptOf t.1))

def SigRowsC : Prop :=
  (∀ ρ, Summable (fun t : ClassT X Y u u' κ ρ =>
    ‖(((Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u) t.1.lam) : ℝ) : ℂ) * Formalism.L2.SG.PairVal.cTerm vR t.1) •
      Formalism.L2.SG.PackageTie.hsEmb (Formalism.L2.SG.RealObj.unscaledOperatorAtPointRepresentative X u u' 1 i0 i0' νq (Formalism.L2.SG.PairVal.ptOf t.1))‖)) ∧
  Summable (fun ρ => ‖clsVec X Y u u' vR i0 i0' νq κ ρ‖ ^ 2) ∧
    (bCF X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq).c0 *
        (bCF X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq).c0' *
        SigOf (Y.tO u u') = ∑' ρ, ‖clsVec X Y u u' vR i0 i0' νq κ ρ‖ ^ 2

def RowVecC : Prop :=
  ∀ ρ, (∑' p : Formalism.FourierDecayAlt.TB.Pt D.host.E,
      Formalism.L2.SG.DataInst.rowVec vR κ (nc * ∏' q, Formalism.L2.SG.DataInst.alpD u u' q) ρ p •
        Formalism.L2.SG.RealObj.VtPt X u u' 1 i0 i0' (Y.FN u) (Y.FN u') νq p) =
      ((Real.sqrt (ngFac D / (Formalism.L2.SG.MassDataConc.kapN D * (nc * ∏' q, Formalism.L2.SG.DataInst.alpD u u' q) *
          Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) (Y.what₂ u))) : ℝ) : ℂ) •
        clsVec X Y u u' vR i0 i0' νq κ ρ

abbrev LiftT (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) : Type :=
  {s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') //
    (Y.tO u u').G s ≠ 0 ∧ (Y.tO u u').gener s ∧ (Y.tO u u').rowOf s = R ∧ κ s.toTerm = ρ}

def ScalTC : Prop :=
  ∀ s₁ s₂ : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'),
    (Y.tO u u').G s₁ ≠ 0 → (Y.tO u u').G s₂ ≠ 0 → (Y.tO u u').gener s₁ → (Y.tO u u').gener s₂ →
    (Y.tO u u').rowOf s₁ = (Y.tO u u').rowOf s₂ →
      (((Y.tO u u').s0 s₁ s₂ = 1 ∧ (Y.tO u u').scal s₁ s₂) ↔ κ s₁.toTerm = κ s₂.toTerm)

def liftVec (s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) :
    Formalism.L2.SG.PackageTie.HS (X.Vpi u') (X.Vpi u) :=
  ((Formalism.L2.SG.TermOp.wt s : ℝ) : ℂ) • Formalism.L2.SG.PackageTie.hsEmb (Formalism.L2.SG.TermOp.ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') s)

def RowRegroupC : Prop :=
  (∀ q : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR × ℕ,
      Summable (fun s : LiftT X Y u u' κ q.1 q.2 => ‖liftVec X Y u u' s.1‖)) ∧
    Summable (fun q : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR × ℕ =>
      ‖∑' s : LiftT X Y u u' κ q.1 q.2, liftVec X Y u u' s.1‖ ^ 2) ∧
    SigOf (Y.tO u u') = ∑' q : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR × ℕ,
      ‖∑' s : LiftT X Y u u' κ q.1 q.2, liftVec X Y u u' s.1‖ ^ 2

def liftVal (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) : Formalism.L2.SG.PackageTie.HS (X.Vpi u') (X.Vpi u) :=
  ∑' s : LiftT X Y u u' κ R ρ,
    ((Formalism.L2.SG.TermOp.wt s.1 : ℝ) * Formalism.L2.SG.PairVal.cTerm vR s.1.toTerm : ℂ) •
      Formalism.L2.SG.PackageTie.hsEmb (Formalism.L2.SG.RealObj.unscaledOperatorAtPointRepresentative X u u' 1 i0 i0' νq (Formalism.L2.SG.PairVal.ptOf s.1.toTerm))

def ClassFrameC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ),
    ‖∑' s : LiftT X Y u u' κ R ρ, liftVec X Y u u' s.1‖ ^ 2 =
      ((bCF X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq).c0 *
          (bCF X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq).c0')⁻¹ *
        ‖liftVal X Y u u' vR i0 i0' νq κ R ρ‖ ^ 2

def TorsorC : Prop :=
  ∀ ρ, Summable (fun R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR => ‖liftVal X Y u u' vR i0 i0' νq κ R ρ‖ ^ 2) ∧
    ∑' R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR, ‖liftVal X Y u u' vR i0 i0' νq κ R ρ‖ ^ 2 =
      ‖clsVec X Y u u' vR i0 i0' νq κ ρ‖ ^ 2

def ClassAbsC : Prop :=
  ∀ ρ, Summable (fun t : ClassT X Y u u' κ ρ =>
    ‖(((Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u) t.1.lam) : ℝ) : ℂ) * Formalism.L2.SG.PairVal.cTerm vR t.1) •
      Formalism.L2.SG.PackageTie.hsEmb (Formalism.L2.SG.RealObj.unscaledOperatorAtPointRepresentative X u u' 1 i0 i0' νq (Formalism.L2.SG.PairVal.ptOf t.1))‖)

def AlTieC : Prop :=
  (bCF X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq).al =
    ∏' q, Formalism.L2.SG.DataInst.alpD u u' q

def ptVal (ρ : ℕ) (p : Formalism.FourierDecayAlt.TB.Pt D.host.E) : Formalism.L2.SG.PackageTie.HS (X.Vpi u') (X.Vpi u) :=
  match Formalism.L2.SG.DataInst.ptOfList (D := D) (D.R.rS + 1) p with
  | some w => (∑' t : {t : Term D u u' (X.Fu u) (Y.what₂ u) // Formalism.L2.SG.DataInst.Elig t ∧ κ t = ρ ∧ t.atPt w},
        ((Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u) t.1.lam) : ℝ) : ℂ) * Formalism.L2.SG.PairVal.cAt vR t.1 w) •
      Formalism.L2.SG.PackageTie.hsEmb (Formalism.L2.SG.RealObj.unscaledOperatorAtPointRepresentative X u u' 1 i0 i0' νq w)
  | none => 0

def WeightConstC (c : ℝ) : Prop :=
  0 < c → ∀ (p : Formalism.FourierDecayAlt.TB.Pt D.host.E) (w : Point D.host.E (D.R.rS + 1)),
    Formalism.L2.SG.DataInst.ptOfList (D := D) (D.R.rS + 1) p = some w →
    (∃ t : Term D u u' (X.Fu u) (Y.what₂ u), Formalism.L2.SG.DataInst.Elig t ∧ t.atPt w) →
    0 < Formalism.L2.SG.DataInst.phi (D := D) (D.R.rS + 1) p ∧
    0 < Formalism.MainNotions.S.LocalSplitGroups.n0 c (D.mem u).A.T (D.mem u').A.T w ∧
    Formalism.L2.SG.RealObj.nW X u u' w = ngFac D / (Formalism.L2.SG.MassDataConc.kapN D * c) *
      (Formalism.MainNotions.S.LocalSplitGroups.n0 c (D.mem u).A.T (D.mem u').A.T w * Formalism.L2.SG.DataInst.phi (D := D) (D.R.rS + 1) p ^ 2)

def PointRegroupC : Prop :=
  ∀ ρ, ∑' p : Formalism.FourierDecayAlt.TB.Pt D.host.E, ptVal X Y u u' vR i0 i0' νq κ ρ p = clsVec X Y u u' vR i0 i0' νq κ ρ

end Formalism.L2.SG.Pf.RowForm

namespace Formalism.L2.SG.Pf

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.MassDataForm Formalism.L2.SG.Pf.RowForm MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rowForm_alg (c S n0c g κ nc α mR : ℝ) (hN : nc = n0c * g / (α * κ)) (hnc : 0 < nc) (hα : 0 < α) (hκ : 0 < κ)
    (hm : 0 < mR) (hg : 0 < g) : c * (S / mR) = n0c * (g / (κ * (nc * α) * mR) * (c * S)) := by
  have hn0 : n0c ≠ 0 := by
    rintro rfl
    rw [hN] at hnc
    simp at hnc
  subst hN
  field_simp
  try ring

theorem rowFormC_of {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (Y : Formalism.L2.SG.Full.Full X)
    (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
    (vR : Term D u u' (X.Fu u) (Y.what₂ u) → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' (X.Fu u) (Y.what₂ u))
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (κ : Term D u u' (X.Fu u) (Y.what₂ u) → ℕ) (nc : ℝ)
    (hS : SigRowsC X hb Y u u' X0 ψ sd C Th vR Q M δ i0 i0' νq κ)
    (hV : RowVecC X Y u u' vR i0 i0' νq κ nc)
    (hN : NcTieC X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq nc)
    (hR : RhoTieC X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq)
    (hA : AlTieC X hb Y u u' X0 ψ sd C Th vR Q M δ i0 i0' νq)
    (hnc : 0 < nc) (hα : 0 < ∏' q, Formalism.L2.SG.DataInst.alpD u u' q) (hk : 0 < Formalism.L2.SG.MassDataConc.kapN D)
    (hm : 0 < Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) (Y.what₂ u)) (hg : 0 < ngFac D) :
    RowFormC X hb Y u u' X0 ψ sd C Th vR Q M δ i0 i0' νq κ nc := by
  have hKpos : 0 < ngFac D / (Formalism.L2.SG.MassDataConc.kapN D * (nc * ∏' q, Formalism.L2.SG.DataInst.alpD u u' q) *
      Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) (Y.what₂ u)) :=
    div_pos hg (mul_pos (mul_pos hk (mul_pos hnc hα)) hm)
  have hrow : ∀ ρ, rowNorm X Y u u' vR i0 i0' νq κ nc ρ =
      ngFac D / (Formalism.L2.SG.MassDataConc.kapN D * (nc * ∏' q, Formalism.L2.SG.DataInst.alpD u u' q) *
        Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) (Y.what₂ u)) * ‖clsVec X Y u u' vR i0 i0' νq κ ρ‖ ^ 2 := by
    intro ρ
    unfold rowNorm
    rw [hV ρ, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt hKpos.le]
  refine ⟨(hS.2.1.mul_left _).congr fun ρ => (hrow ρ).symm, ?_⟩
  rw [tsum_congr hrow, tsum_mul_left, ← hS.2.2]
  have hKV : (bCF X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq).KV =
      SigOf (Y.tO u u') / (bCF X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq).ρ0 := rfl
  rw [hKV, hR]
  unfold NcTieC at hN
  rw [hA] at hN
  exact rowForm_alg _ _ _ _ _ _ _ _ hN hnc hα hk hm hg

theorem sigRowsC_of {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (Y : Formalism.L2.SG.Full.Full X)
    (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
    (vR : Term D u u' (X.Fu u) (Y.what₂ u) → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' (X.Fu u) (Y.what₂ u))
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (κ : Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)
    (hRR : RowRegroupC X Y u u' κ) (hCF : ClassFrameC X hb Y u u' X0 ψ sd C Th vR Q M δ i0 i0' νq κ)
    (hTor : TorsorC X Y u u' vR i0 i0' νq κ) (hCA : ClassAbsC X Y u u' vR i0 i0' νq κ)
    (hc : 0 < (bCF X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq).c0 *
      (bCF X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq).c0') :
    SigRowsC X hb Y u u' X0 ψ sd C Th vR Q M δ i0 i0' νq κ := by
  unfold SigRowsC
  unfold ClassFrameC at hCF
  generalize hcdef : (bCF X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq).c0 *
    (bCF X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq).c0' = c at hCF hc ⊢
  have hG : ∀ q : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR × ℕ,
      ‖liftVal X Y u u' vR i0 i0' νq κ q.1 q.2‖ ^ 2 =
        c * ‖∑' s : LiftT X Y u u' κ q.1 q.2, liftVec X Y u u' s.1‖ ^ 2 := by
    intro q
    rw [hCF q.1 q.2, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
  have hGs : Summable (fun q : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR × ℕ =>
      ‖liftVal X Y u u' vR i0 i0' νq κ q.1 q.2‖ ^ 2) :=
    (hRR.2.1.mul_left c).congr fun q => (hG q).symm
  have hGs' : Summable (fun p : ℕ × Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR =>
      ‖liftVal X Y u u' vR i0 i0' νq κ p.2 p.1‖ ^ 2) :=
    (Equiv.prodComm _ _).summable_iff.mpr hGs
  have hcls : ∀ ρ, ‖clsVec X Y u u' vR i0 i0' νq κ ρ‖ ^ 2 =
      ∑' R, ‖liftVal X Y u u' vR i0 i0' νq κ R ρ‖ ^ 2 := fun ρ => (hTor ρ).2.symm
  refine ⟨hCA, (hGs'.prod).congr fun ρ => (hcls ρ).symm, ?_⟩
  have h1 : c * SigOf (Y.tO u u') =
      ∑' q : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR × ℕ, ‖liftVal X Y u u' vR i0 i0' νq κ q.1 q.2‖ ^ 2 := by
    rw [hRR.2.2, ← tsum_mul_left]
    exact tsum_congr fun q => (hG q).symm
  have h2 : (∑' q : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR × ℕ,
      ‖liftVal X Y u u' vR i0 i0' νq κ q.1 q.2‖ ^ 2) =
      ∑' p : ℕ × Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR, ‖liftVal X Y u u' vR i0 i0' νq κ p.2 p.1‖ ^ 2 :=
    (Equiv.prodComm _ _).tsum_eq (fun p : ℕ × Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR =>
      ‖liftVal X Y u u' vR i0 i0' νq κ p.2 p.1‖ ^ 2)
  rw [h1, h2, hGs'.tsum_prod' fun ρ => (hTor ρ).1]
  exact tsum_congr fun ρ => (hcls ρ).symm

theorem rowVecC_of {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
    (vR : Term D u u' (X.Fu u) (Y.what₂ u) → ℝ)
    (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (κ : Term D u u' (X.Fu u) (Y.what₂ u) → ℕ) (nc : ℝ)
    (hW : WeightConstC X Y u u' (nc * ∏' q, Formalism.L2.SG.DataInst.alpD u u' q))
    (hP : PointRegroupC X Y u u' vR i0 i0' νq κ)
    (hm : 0 < Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) (Y.what₂ u)) (hk : 0 < Formalism.L2.SG.MassDataConc.kapN D)
    (hc : 0 < nc * ∏' q, Formalism.L2.SG.DataInst.alpD u u' q) (hg : 0 < ngFac D) :
    RowVecC X Y u u' vR i0 i0' νq κ nc := by
  intro ρ
  set c := nc * ∏' q, Formalism.L2.SG.DataInst.alpD u u' q with hcdef
  set mR := Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) (Y.what₂ u) with hmR
  set K0 := ngFac D / (Formalism.L2.SG.MassDataConc.kapN D * c) with hK0
  have hK0pos : 0 < K0 := div_pos hg (mul_pos hk hc)
  have hKeq : ngFac D / (Formalism.L2.SG.MassDataConc.kapN D * c * mR) = K0 / mR := by
    rw [hK0, div_div]
  have hpt : ∀ p : Formalism.FourierDecayAlt.TB.Pt D.host.E,
      Formalism.L2.SG.DataInst.rowVec vR κ c ρ p • Formalism.L2.SG.RealObj.VtPt X u u' 1 i0 i0' (Y.FN u) (Y.FN u') νq p =
        ((Real.sqrt (K0 / mR) : ℝ) : ℂ) • ptVal X Y u u' vR i0 i0' νq κ ρ p := by
    intro p
    unfold Formalism.L2.SG.DataInst.rowVec Formalism.L2.SG.RealObj.VtPt Formalism.L2.SG.RealObj.ptOfL ptVal
    cases hp : (Formalism.L2.SG.DataInst.ptOfList (D.R.rS + 1) p : Option (Point D.host.E (D.R.rS + 1))) with
    | none => simp
    | some w =>
      simp only
      by_cases hex : ∃ t : Term D u u' (X.Fu u) (Y.what₂ u), Formalism.L2.SG.DataInst.Elig t ∧ κ t = ρ ∧ t.atPt w
      · obtain ⟨t0, he, -, hat⟩ := hex
        obtain ⟨hφ, hn0, hnW⟩ := hW hc p w hp ⟨t0, he, hat⟩
        have hA : (∑' t : {t : Term D u u' (X.Fu u) (Y.what₂ u) // Formalism.L2.SG.DataInst.Elig t ∧ κ t = ρ ∧ t.atPt w},
            ((Real.sqrt (Formalism.L2.SG.PairVal.massTerm t.1) : ℝ) : ℂ) * Formalism.L2.SG.PairVal.cAt vR t.1 w) =
            (((Real.sqrt mR)⁻¹ : ℝ) : ℂ) *
              ∑' t : {t : Term D u u' (X.Fu u) (Y.what₂ u) // Formalism.L2.SG.DataInst.Elig t ∧ κ t = ρ ∧ t.atPt w},
                ((Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u) t.1.lam) : ℝ) : ℂ) * Formalism.L2.SG.PairVal.cAt vR t.1 w := by
          rw [← tsum_mul_left]
          refine tsum_congr fun t => ?_
          have hmt : Formalism.L2.SG.PairVal.massTerm t.1 = Formalism.MainNotions.S.wRow D (X.Fu u) t.1.lam / mR := rfl
          rw [hmt, Real.sqrt_div' _ hm.le]
          push_cast
          ring
        rw [hA, smul_smul, smul_smul, hnW]
        congr 1
        have e1 : Real.sqrt (K0 * (Formalism.MainNotions.S.LocalSplitGroups.n0 c (D.mem u).A.T (D.mem u').A.T w *
            Formalism.L2.SG.DataInst.phi (D := D) (D.R.rS + 1) p ^ 2)) =
            Real.sqrt K0 * Real.sqrt (Formalism.MainNotions.S.LocalSplitGroups.n0 c (D.mem u).A.T (D.mem u').A.T w) *
              Formalism.L2.SG.DataInst.phi (D := D) (D.R.rS + 1) p := by
          rw [Real.sqrt_mul hK0pos.le, Real.sqrt_mul hn0.le, Real.sqrt_sq hφ.le]
          ring
        have e2 : Real.sqrt (K0 / mR) = Real.sqrt K0 / Real.sqrt mR := Real.sqrt_div' _ hm.le
        rw [e1, e2]
        have h1 : Real.sqrt (Formalism.MainNotions.S.LocalSplitGroups.n0 c (D.mem u).A.T (D.mem u').A.T w) ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
        have h2 : Real.sqrt mR ≠ 0 := (Real.sqrt_pos.mpr hm).ne'
        have h3 : Formalism.L2.SG.DataInst.phi (D := D) (D.R.rS + 1) p ≠ 0 := hφ.ne'
        have h1' : ((Real.sqrt (Formalism.MainNotions.S.LocalSplitGroups.n0 c (D.mem u).A.T (D.mem u').A.T w) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h1
        have h2' : ((Real.sqrt mR : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h2
        have h3' : ((Formalism.L2.SG.DataInst.phi (D := D) (D.R.rS + 1) p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h3
        push_cast
        field_simp
      · have hE : IsEmpty {t : Term D u u' (X.Fu u) (Y.what₂ u) // Formalism.L2.SG.DataInst.Elig t ∧ κ t = ρ ∧ t.atPt w} :=
          ⟨fun t => hex ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩⟩
        simp [tsum_empty]
  calc ∑' p : Formalism.FourierDecayAlt.TB.Pt D.host.E,
        Formalism.L2.SG.DataInst.rowVec vR κ c ρ p • Formalism.L2.SG.RealObj.VtPt X u u' 1 i0 i0' (Y.FN u) (Y.FN u') νq p
      = ∑' p : Formalism.FourierDecayAlt.TB.Pt D.host.E, ((Real.sqrt (K0 / mR) : ℝ) : ℂ) • ptVal X Y u u' vR i0 i0' νq κ ρ p :=
        tsum_congr hpt
    _ = ((Real.sqrt (K0 / mR) : ℝ) : ℂ) • ∑' p : Formalism.FourierDecayAlt.TB.Pt D.host.E, ptVal X Y u u' vR i0 i0' νq κ ρ p :=
        tsum_const_smul'' _
    _ = ((Real.sqrt (K0 / mR) : ℝ) : ℂ) • clsVec X Y u u' vR i0 i0' νq κ ρ := by rw [hP ρ]
    _ = _ := by rw [hKeq]

end Formalism.L2.SG.Pf
