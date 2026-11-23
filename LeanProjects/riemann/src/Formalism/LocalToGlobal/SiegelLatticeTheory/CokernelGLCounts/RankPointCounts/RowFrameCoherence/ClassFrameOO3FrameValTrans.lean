import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DecompPhaseCOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.ClassFrameOO1FrameValPiIso

noncomputable section

open scoped Classical ComplexConjugate

namespace Formalism.L2.SG.Pf.RowForm.ClassFrameLeviDecomposition

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem pi_levi (w : D.what₂.Word) {n a h : X.B.I.Ginf} (hn : n ∈ X.NinfU w) (ha : a ∈ Formalism.L2.SG.RealObj.HsetU X w)
    (hh : h ∈ X.SinfU w) : X.piU w (a * h) = (X.piU w (n * a)).comp (X.piU w h) := by
  have hnS : n ∈ X.SinfU w := fun v => (hn v).1
  have haS := Formalism.L2.SG.RealObj.InfCut.hsetU_sub X w ha
  rw [(X.piU_rep w).2.1 a haS h hh, (X.piU_rep w).2.1 n hnS a haS, (X.piU_rep w).2.2.2.1 n hn, one_mul]
  rfl

end Formalism.L2.SG.Pf.RowForm.ClassFrameLeviDecomposition

namespace Formalism.L2.SG.Pf.RowForm

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.MassDataForm MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
  (vR : Term D u u' (X.Fu u) (Y.what₂ u) → ℝ)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
  (κ : Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)

def decVal (g g' h h' : X.B.I.Ginf) (s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) :
    X.Vpi u' →L[ℂ] X.Vpi u :=
  Formalism.L2.SG.PairVal.cTerm vR s.toTerm •
    ((X.piU u g).comp ((X.piU u h).comp ((Formalism.L2.SG.RealObj.unscaledOperatorAtPointRepresentative X u u' 1 i0 i0' νq (Formalism.L2.SG.PairVal.ptOf s.toTerm)).comp
      ((X.piU u' h'⁻¹).comp (X.piU u' g'⁻¹)))))

def CommonDC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ),
    ∃ (U : X.Vpi u ≃ₗᵢ[ℂ] X.Vpi u) (U' : X.Vpi u' ≃ₗᵢ[ℂ] X.Vpi u') (ζ : ℂ), ‖ζ‖ = 1 ∧
      ∀ s : LiftT X Y u u' κ R ρ, s.1.relevant →
        ∀ g ∈ X.SinfU u, ∀ g' ∈ X.SinfU u',
          s.1.pt.1 = g * Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) * g'⁻¹ →
          ∀ h h', Formalism.L2.SG.RealObj.IsDFrameX X u u' 1 i0 i0'
              (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm)) h h' →
            decVal X Y u u' vR i0 i0' νq g g' h h' s.1 = ζ • frameVal X Y u u' vR i0 i0' νq U U' s.1

theorem classFrameOO3_frameVal_trans (g g' h h' : X.B.I.Ginf) (hg : g ∈ X.SinfU u) (hg' : g' ∈ X.SinfU u')
    (hh : h ∈ X.SinfU u) (hh' : h' ∈ X.SinfU u')
    (s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) :
    frameVal X Y u u' vR i0 i0' νq ((Formalism.L2.SG.RealObj.InfCut.piIso X u h hh).trans (Formalism.L2.SG.RealObj.InfCut.piIso X u g hg))
      ((Formalism.L2.SG.RealObj.InfCut.piIso X u' h' hh').trans (Formalism.L2.SG.RealObj.InfCut.piIso X u' g' hg')) s =
      decVal X Y u u' vR i0 i0' νq g g' h h' s := by
  have hs : ∀ (w : D.what₂.Word) (a : X.B.I.Ginf) (ha : a ∈ X.SinfU w) (y : X.Vpi w),
      (Formalism.L2.SG.RealObj.InfCut.piIso X w a ha).symm y = X.piU w a⁻¹ y := fun w a ha y => by
    have := congrArg (fun T : X.Vpi w →L[ℂ] X.Vpi w => T y) (Formalism.L2.SG.RealObj.InfCut.piIso_symm X w a ha)
    exact this
  unfold frameVal decVal
  congr 1
  ext x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.symm_trans, Formalism.L2.SG.RealObj.InfCut.piIso_apply, hs]

theorem chiOO_decomp (h1 : LiftAtSomeC X Y u u' κ)
    (h2 : Formalism.L2.SG.PairVal.CellPtUnique D u u' (X.Fu u) (Y.what₂ u))
    (h3 : DecompPhaseC X Y u u' κ) (h4 : DFrameAtS X u u' i0 i0' 1) (h4' : LiftGPosC X Y u u' κ)
    (h5 : FormTranspC X Y u u' vR νq κ)
    (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s : LiftT X Y u u' κ R ρ) (hrel : s.1.relevant) :
    ∃ g ∈ X.SinfU u, ∃ g' ∈ X.SinfU u',
      s.1.pt.1 = g * Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) * g'⁻¹ ∧
      ∃ h h', Formalism.L2.SG.RealObj.IsDFrameX X u u' 1 i0 i0'
          (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm)) h h' ∧
        chiOO X Y u u' s.1 = decVal X Y u u' vR i0 i0' νq g g' h h' s.1 := by
  obtain ⟨hpt, g, hg, g', hg', hdec, hph⟩ := h3 R ρ s hrel
  have hDF : ∃ p : X.B.I.Ginf × X.B.I.Ginf, Formalism.L2.SG.RealObj.IsDFrameX X u u' 1 i0 i0'
      (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm)) p.1 p.2 := by
    obtain ⟨h, h', hh⟩ := h4 one_pos _ hpt (h4' R ρ s hrel)
    exact ⟨(h, h'), hh⟩
  have hcS : hDF.choose.1 ∈ X.SinfU u := Formalism.L2.SG.RealObj.InfCut.hsetU_sub X u hDF.choose_spec.1
  have hcS' : hDF.choose.2 ∈ X.SinfU u' := Formalism.L2.SG.RealObj.InfCut.hsetU_sub X u' hDF.choose_spec.2.1
  have hcSi : hDF.choose.1⁻¹ ∈ X.SinfU u := Formalism.L2.SG.RealObj.InfCut.sinfU_inv X u hcS
  refine ⟨g, hg, g', hg', hdec, hDF.choose.1, hDF.choose.2, hDF.choose_spec, ?_⟩
  rw [← classFrameOO3_frameVal_trans X Y u u' vR i0 i0' νq g g' _ _ hg hg' hcS hcS']
  have hat : s.1.toTerm.atPt (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) := by
    obtain ⟨w0, hw0⟩ := h1 R ρ s hrel
    exact Formalism.L2.SG.PairVal.ptOf_spec _ ⟨w0, hw0, hrel⟩
  have hcT : Formalism.L2.SG.PairVal.cTerm vR s.1.toTerm =
      Formalism.L2.SG.PairVal.phaseAt s.1.toTerm (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) * (vR s.1.toTerm : ℂ) :=
    Formalism.L2.SG.PairVal.cTerm_of_atPt vR _ hat (fun w' hw' => h2 _ w' _ hw' hat)
  have hV : Formalism.L2.SG.RealObj.unscaledOperatorAtPointRepresentative X u u' 1 i0 i0' νq (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) =
      (X.piU u hDF.choose.1⁻¹).comp ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
        Formalism.L2.SG.TermOp.OO (νq (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm))) Set.univ
          (X.Wu u) (X.Wu u') (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm))).comp
        (X.piU u' hDF.choose.2)) := by
    unfold Formalism.L2.SG.RealObj.unscaledOperatorAtPointRepresentative Formalism.L2.SG.RealObj.unscaledFrameConjugatedOperator
    rw [if_pos hpt, dif_pos hDF]
  have hO : Formalism.L2.SG.TermOp.OOt s.1 =
      (((vR s.1.toTerm : ℝ) : ℂ) * (X.psiInfU u g * conj (X.psiInfU u' g'))) •
        (((Formalism.L2.SG.RealObj.InfCut.piIso X u g hg).toContinuousLinearEquiv : X.Vpi u →L[ℂ] X.Vpi u).comp
          ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
            Formalism.L2.SG.TermOp.OO (νq (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm))) Set.univ
              (X.Wu u) (X.Wu u') (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm))).comp
            ((Formalism.L2.SG.RealObj.InfCut.piIso X u' g' hg').symm.toContinuousLinearEquiv : X.Vpi u' →L[ℂ] X.Vpi u'))) := by
    rw [h5 R ρ s hrel g hg g' hg' hdec, ← smul_smul]
    congr 1
    rw [hdec]
    exact ClassFrameNormal.oo_map_mulLeft _ _ _ _ g g' _ _ _ _
      (fun x => (X.Wu_spec u).1 g hg x) (fun x => (X.Wu_spec u').1 g' hg' x)
  have e1 : ∀ z, X.piU u hDF.choose.1 (X.piU u hDF.choose.1⁻¹ z) = z := fun z =>
    ClassFrameUnitaryProducts.piU_mul_inv_apply X u hcS z
  have e2 : ∀ y, X.piU u' hDF.choose.2 ((Formalism.L2.SG.RealObj.InfCut.piIso X u' hDF.choose.2 hcS').symm y) = y :=
    fun y => (Formalism.L2.SG.RealObj.InfCut.piIso X u' hDF.choose.2 hcS').apply_symm_apply y
  unfold chiOO frameVal
  rw [hO, hcT, hV, smul_smul, ← hph]
  have hsc : ∀ a c r : ℂ, a * (r * c) = a * c * r := fun a c r => by ring
  rw [hsc]
  congr 1
  ext x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.symm_trans, Formalism.L2.SG.RealObj.InfCut.piIso_apply, e1, e2]

def DFrameMoveC : Prop :=
  ∀ γ h h' g g' : X.B.I.Ginf, Formalism.L2.SG.RealObj.IsDFrameX X u u' 1 i0 i0' γ h h' → g ∈ X.SinfU u → g' ∈ X.SinfU u' →
    ∃ k k', Formalism.L2.SG.RealObj.IsDFrameX X u u' 1 i0 i0' (g * γ * g'⁻¹) k k' ∧
      X.piU u k = (X.piU u g).comp (X.piU u h) ∧ X.piU u' k' = (X.piU u' g').comp (X.piU u' h')

def SDecompC (w : D.what₂.Word) : Prop :=
  ∀ g ∈ X.SinfU w, ∃ n ∈ X.NinfU w, ∃ a ∈ Formalism.L2.SG.RealObj.HsetU X w, g = n * a

def DFrameMoveHC : Prop :=
  ∀ γ h h' n a n' a' : X.B.I.Ginf, Formalism.L2.SG.RealObj.IsDFrameX X u u' 1 i0 i0' γ h h' →
    n ∈ X.NinfU u → a ∈ Formalism.L2.SG.RealObj.HsetU X u → n' ∈ X.NinfU u' → a' ∈ Formalism.L2.SG.RealObj.HsetU X u' →
      Formalism.L2.SG.RealObj.IsDFrameX X u u' 1 i0 i0' (n * a * γ * a'⁻¹ * n'⁻¹) (a * h) (a' * h')

theorem dFrameMoveC_of (hS : SDecompC X u) (hS' : SDecompC X u') (hM : DFrameMoveHC X u u' i0 i0') :
    DFrameMoveC X u u' i0 i0' := by
  intro γ h h' g g' hD hg hg'
  obtain ⟨n, hn, a, ha, rfl⟩ := hS g hg
  obtain ⟨n', hn', a', ha', rfl⟩ := hS' g' hg'
  refine ⟨a * h, a' * h', ?_, ?_, ?_⟩
  · have e : n * a * γ * (n' * a')⁻¹ = n * a * γ * a'⁻¹ * n'⁻¹ := by group
    rw [e]
    exact hM γ h h' n a n' a' hD hn ha hn' ha'
  · exact Formalism.L2.SG.Pf.RowForm.ClassFrameLeviDecomposition.pi_levi X u hn ha (Formalism.L2.SG.RealObj.InfCut.hsetU_sub X u hD.1)
  · exact Formalism.L2.SG.Pf.RowForm.ClassFrameLeviDecomposition.pi_levi X u' hn' ha' (Formalism.L2.SG.RealObj.InfCut.hsetU_sub X u' hD.2.1)

theorem ptValueC_of (h1 : LiftAtSomeC X Y u u' κ)
    (h2 : Formalism.L2.SG.PairVal.CellPtUnique D u u' (X.Fu u) (Y.what₂ u))
    (h3 : DecompPhaseC X Y u u' κ) (h4 : DFrameAtS X u u' i0 i0' 1) (h4' : LiftGPosC X Y u u' κ)
    (h5 : FormTranspC X Y u u' vR νq κ) (hM : DFrameMoveC X u u' i0 i0') :
    PtValueC X Y u u' vR i0 i0' νq κ := by
  intro R ρ s hrel
  obtain ⟨g, hg, g', hg', hdec, h, h', hDF, hval⟩ := chiOO_decomp X Y u u' vR i0 i0' νq κ h1 h2 h3 h4 h4' h5 R ρ s hrel
  obtain ⟨k, k', hK, hk, hk'⟩ := hM _ h h' g g' hDF hg hg'
  refine ⟨k, k', hdec ▸ hK, ?_⟩
  have hkS : k ∈ X.SinfU u := Formalism.L2.SG.RealObj.InfCut.hsetU_sub X u hK.1
  have hki : k⁻¹ ∈ X.SinfU u := Formalism.L2.SG.RealObj.InfCut.sinfU_inv X u hkS
  have hgi : g'⁻¹ ∈ X.SinfU u' := Formalism.L2.SG.RealObj.InfCut.sinfU_inv X u' hg'
  have hhi : h'⁻¹ ∈ X.SinfU u' :=
    Formalism.L2.SG.RealObj.InfCut.sinfU_inv X u' (Formalism.L2.SG.RealObj.InfCut.hsetU_sub X u' hDF.2.1)
  have c1 : ∀ y, X.piU u k⁻¹ (X.piU u k y) = y := fun y => by
    have := ClassFrameUnitaryProducts.piU_mul_inv_apply X u hki y
    rwa [inv_inv] at this
  have c2 : ∀ y, X.piU u' g'⁻¹ (X.piU u' g' y) = y := fun y => by
    have := ClassFrameUnitaryProducts.piU_mul_inv_apply X u' hgi y
    rwa [inv_inv] at this
  have c3 : ∀ y, X.piU u' h'⁻¹ (X.piU u' h' y) = y := fun y => by
    have := ClassFrameUnitaryProducts.piU_mul_inv_apply X u' hhi y
    rwa [inv_inv] at this
  have hk1 : ∀ y, X.piU u g (X.piU u h y) = X.piU u k y := fun y => by rw [hk]; rfl
  have hk2 : ∀ y, X.piU u' k' y = X.piU u' g' (X.piU u' h' y) := fun y => by rw [hk']; rfl
  rw [hval]
  unfold decVal
  ext x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, map_smul, hk2, c2, c3, hk1, c1]

theorem commonFrameC_of_D (h1 : LiftAtSomeC X Y u u' κ)
    (h2 : Formalism.L2.SG.PairVal.CellPtUnique D u u' (X.Fu u) (Y.what₂ u))
    (h3 : DecompPhaseC X Y u u' κ) (h4 : DFrameAtS X u u' i0 i0' 1) (h4' : LiftGPosC X Y u u' κ)
    (h5 : FormTranspC X Y u u' vR νq κ) (hD : CommonDC X Y u u' vR i0 i0' νq κ)
    (hV : LemmaVLiftC X Y u u' κ) (hAt : AtPtRelevantC X Y u u') :
    CommonFrameC X Y u u' vR i0 i0' νq κ := by
  intro R ρ
  obtain ⟨U, U', ζ, hζ, hc⟩ := hD R ρ
  refine ⟨U, U', ζ, hζ, fun s A B hAB => ?_⟩
  rw [← hAB]
  by_cases hrel : s.1.relevant
  · obtain ⟨g, hg, g', hg', hdec, h, h', hDF, hval⟩ :=
      chiOO_decomp X Y u u' vR i0 i0' νq κ h1 h2 h3 h4 h4' h5 R ρ s hrel
    rw [hval]
    exact hc s hrel g hg g' hg' hdec h h' hDF
  · obtain ⟨h0, hc0⟩ := irrelZeroC_of X Y u u' vR i0 i0' νq κ hV hAt R ρ s hrel
    rw [h0]
    unfold frameVal
    rcases hc0 with hc0 | hc0
    · rw [hc0, zero_smul, smul_zero]
    · rw [hc0]
      simp

theorem commonFrameC_of_move (h1 : LiftAtSomeC X Y u u' κ)
    (h2 : Formalism.L2.SG.PairVal.CellPtUnique D u u' (X.Fu u) (Y.what₂ u))
    (h3 : DecompPhaseC X Y u u' κ) (h4 : DFrameAtS X u u' i0 i0' 1) (h4' : LiftGPosC X Y u u' κ)
    (h5 : FormTranspC X Y u u' vR νq κ) (hM : DFrameMoveC X u u' i0 i0') (hF : OOtNuC X Y u u' νq κ)
    (hNu : Formalism.L2.SG.RealObj.NuQOK X u u' νq) (hVI : Formalism.L2.SG.RealObj.VIndep X u u' 1 i0 i0' νq)
    (hS : ScalarAgreeC X Y u u' κ) (hV : LemmaVLiftC X Y u u' κ) (hAt : AtPtRelevantC X Y u u') :
    CommonFrameC X Y u u' vR i0 i0' νq κ :=
  commonFrameC_of_scalar X Y u u' vR i0 i0' νq κ (ptValueC_of X Y u u' vR i0 i0' νq κ h1 h2 h3 h4 h4' h5 hM) hF hNu hVI
    hS hV hAt

end Formalism.L2.SG.Pf.RowForm
