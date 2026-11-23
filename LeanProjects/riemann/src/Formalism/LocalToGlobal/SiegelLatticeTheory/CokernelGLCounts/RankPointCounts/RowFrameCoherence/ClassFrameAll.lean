import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RealDecompL
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.ClassFrameOO3FrameValTrans
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.ScalarAgreeRatCOfScalT
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.ClassFrameMoveH
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.ClassFrameSDecomp

noncomputable section

open scoped Classical ComplexConjugate

namespace Formalism.L2.SG.Pf.RowForm

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.MassDataForm MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem classFrameAll_comp {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] (P G K : V →L[ℂ] V) (G' H' K' : V' →L[ℂ] V') (T : V' →L[ℂ] V)
    (a : ℂ) (hK : K = P * G) (hK' : K' = G' * H') :
    P.comp ((a • G.comp (T.comp G')).comp H') = a • K.comp (T.comp K') := by
  subst hK hK'
  ext x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply, map_smul]

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (Y : Formalism.L2.SG.Full.Full X)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
  (vR : Term D u u' (X.Fu u) (Y.what₂ u) → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' (X.Fu u) (Y.what₂ u))
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
  (κ : Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)

def VIndepAtC (sc : ℝ) : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), (∃ γ, Formalism.L2.SG.RealObj.IsPtRep X u u' w γ) →
    (∀ v, 0 < Formalism.L2.SG.RealObj.GX X u u' D.host.rdE (Formalism.L2.SG.RealObj.gamW X u u' w) v) →
    ∀ h₁ h₁' h₂ h₂', Formalism.L2.SG.RealObj.IsDFrameX X u u' sc i0 i0' (Formalism.L2.SG.RealObj.gamW X u u' w) h₁ h₁' →
      Formalism.L2.SG.RealObj.IsDFrameX X u u' sc i0 i0' (Formalism.L2.SG.RealObj.gamW X u u' w) h₂ h₂' →
      (X.piU u h₁⁻¹).comp ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
          Formalism.L2.SG.TermOp.OO (νq (Formalism.L2.SG.RealObj.gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u')
            (Formalism.L2.SG.RealObj.gamW X u u' w)).comp (X.piU u' h₁')) =
        (X.piU u h₂⁻¹).comp ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
          Formalism.L2.SG.TermOp.OO (νq (Formalism.L2.SG.RealObj.gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u')
            (Formalism.L2.SG.RealObj.gamW X u u' w)).comp (X.piU u' h₂'))

theorem classFrameAll_pi_inv (w : D.what₂.Word) {k g h : X.B.I.Ginf} (hk : k ∈ X.SinfU w) (hg : g ∈ X.SinfU w)
    (hh : h ∈ X.SinfU w) (e : X.piU w k = X.piU w g⁻¹ * X.piU w h) :
    X.piU w k⁻¹ = X.piU w h⁻¹ * X.piU w g := by
  have rep := X.piU_rep w
  have hki := Formalism.L2.SG.RealObj.InfCut.sinfU_inv X w hk
  have hgi := Formalism.L2.SG.RealObj.InfCut.sinfU_inv X w hg
  have hhi := Formalism.L2.SG.RealObj.InfCut.sinfU_inv X w hh
  have e1 : X.piU w k * (X.piU w h⁻¹ * X.piU w g) = 1 := by
    rw [e, mul_assoc, ← mul_assoc (X.piU w h), ← rep.2.1 h hh h⁻¹ hhi, mul_inv_cancel, rep.1, one_mul,
      ← rep.2.1 g⁻¹ hgi g hg, inv_mul_cancel, rep.1]
  calc X.piU w k⁻¹ = X.piU w k⁻¹ * (X.piU w k * (X.piU w h⁻¹ * X.piU w g)) := by rw [e1, mul_one]
    _ = X.piU w h⁻¹ * X.piU w g := by rw [← mul_assoc, ← rep.2.1 k⁻¹ hki k hk, inv_mul_cancel, rep.1, one_mul]

theorem classFrameAll_pull (γ g g' h h' : X.B.I.Ginf) (hg : g ∈ X.SinfU u) (hg' : g' ∈ X.SinfU u')
    (hD : Formalism.L2.SG.RealObj.IsDFrameX X u u' 1 i0 i0' (g * γ * g'⁻¹) h h') :
    ∃ k k', Formalism.L2.SG.RealObj.IsDFrameX X u u' 1 i0 i0' γ k k' ∧
      X.piU u k⁻¹ = X.piU u h⁻¹ * X.piU u g ∧ X.piU u' k' = X.piU u' g'⁻¹ * X.piU u' h' := by
  have hgi := Formalism.L2.SG.RealObj.InfCut.sinfU_inv X u hg
  have hgi' := Formalism.L2.SG.RealObj.InfCut.sinfU_inv X u' hg'
  obtain ⟨n, hn, a, ha, e⟩ := sDecompC_holds X u g⁻¹ hgi
  obtain ⟨n', hn', a', ha', e'⟩ := sDecompC_holds X u' g'⁻¹ hgi'
  have hM := dFrameMoveHC_holds X u u' i0 i0' _ h h' n a n' a' hD hn ha hn' ha'
  have eγ : n * a * (g * γ * g'⁻¹) * a'⁻¹ * n'⁻¹ = γ := by
    have e0 : n * a * (g * γ * g'⁻¹) * a'⁻¹ * n'⁻¹ = n * a * (g * γ * g'⁻¹) * (n' * a')⁻¹ := by group
    rw [e0, ← e, ← e']
    group
  rw [eγ] at hM
  have hh := Formalism.L2.SG.RealObj.InfCut.hsetU_sub X u hD.1
  have hh' := Formalism.L2.SG.RealObj.InfCut.hsetU_sub X u' hD.2.1
  have hk := Formalism.L2.SG.RealObj.InfCut.hsetU_sub X u hM.1
  have p1 : X.piU u (a * h) = X.piU u g⁻¹ * X.piU u h := by
    rw [ClassFrameLeviDecomposition.pi_levi X u hn ha hh, ← e]
    rfl
  have p2 : X.piU u' (a' * h') = X.piU u' g'⁻¹ * X.piU u' h' := by
    rw [ClassFrameLeviDecomposition.pi_levi X u' hn' ha' hh', ← e']
    rfl
  exact ⟨a * h, a' * h', hM, classFrameAll_pi_inv X u hk hg hh p1, p2⟩

theorem vIndepLiftC_of_at (h3 : LiftDecompC X Y u u' κ) (h4' : LiftGPosC X Y u u' κ)
    (h5 : FormTranspC X Y u u' vR νq κ) (hVA : VIndepAtC X u u' i0 i0' νq 1) :
    VIndepLiftC X Y u u' i0 i0' κ := by
  intro R ρ s hrel h₁ h₁' h₂ h₂' hD₁ hD₂
  obtain ⟨hpt, g, hg, g', hg', hdec⟩ := h3 R ρ s hrel
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
  rw [Formalism.L2.SG.RealObj.InfCut.piIso_coe, Formalism.L2.SG.RealObj.InfCut.piIso_symm] at hO
  rw [hdec] at hD₁ hD₂
  obtain ⟨k₁, k₁', hK₁, e₁, e₁'⟩ := classFrameAll_pull X u u' i0 i0' _ g g' h₁ h₁' hg hg' hD₁
  obtain ⟨k₂, k₂', hK₂, e₂, e₂'⟩ := classFrameAll_pull X u u' i0 i0' _ g g' h₂ h₂' hg hg' hD₂
  have hV := hVA _ hpt (h4' R ρ s hrel) k₁ k₁' k₂ k₂' hK₁ hK₂
  unfold chiOO
  rw [hO, smul_smul, classFrameAll_comp _ _ _ _ _ _ _ _ e₁ e₁', classFrameAll_comp _ _ _ _ _ _ _ _ e₂ e₂', hV]

theorem normalFormC_all
    (hAtS : ∀ t : Term D u u' (X.Fu u) (Y.what₂ u), t.G ≠ 0 → t.relevant → ∃ w, t.atPt w)
    (hTP : ∀ (t : Term D u u' (X.Fu u) (Y.what₂ u)) (w : Point D.host.E (D.R.rS + 1)), t.atPt w →
      TotPos (Gpt (D.mem u).A.T (D.mem u').A.T w))
    (hCU : Formalism.L2.SG.PairVal.CellPtUnique D u u' (X.Fu u) (Y.what₂ u))
    (hDF : DFrameAtS X u u' i0 i0' 1) (hPT : PhaseTieC X Y u u' κ) (hFT : FormTranspC X Y u u' vR νq κ) :
    NormalFormC X Y u u' vR i0 i0' νq κ :=
  normalFormC_of' X Y u u' vR i0 i0' νq κ (RealDecompL.liftAtSomeC_of X Y u u' κ hAtS) hCU
    (decompPhaseC_of X Y u u' κ (RealDecompL.liftDecompC_of_atSome X Y u u' κ hAtS) hPT) hDF
    (RealDecompL.liftGPosC_of X Y u u' κ hAtS hTP) hFT

theorem commonFrameC_all
    (hAtS : ∀ t : Term D u u' (X.Fu u) (Y.what₂ u), t.G ≠ 0 → t.relevant → ∃ w, t.atPt w)
    (hTP : ∀ (t : Term D u u' (X.Fu u) (Y.what₂ u)) (w : Point D.host.E (D.R.rS + 1)), t.atPt w →
      TotPos (Gpt (D.mem u).A.T (D.mem u').A.T w))
    (hCU : Formalism.L2.SG.PairVal.CellPtUnique D u u' (X.Fu u) (Y.what₂ u))
    (hDF : DFrameAtS X u u' i0 i0' 1) (hPT : PhaseTieC X Y u u' κ) (hFT : FormTranspC X Y u u' vR νq κ)
    (hVA : VIndepAtC X u u' i0 i0' νq 1) (hSc : ScalTC X Y u u' κ) (hV : LemmaVLiftC X Y u u' κ)
    (hAt : AtPtRelevantC X Y u u') :
    CommonFrameC X Y u u' vR i0 i0' νq κ := by
  have hLD := RealDecompL.liftDecompC_of_atSome X Y u u' κ hAtS
  have hGP := RealDecompL.liftGPosC_of X Y u u' κ hAtS hTP
  have hP : PtValueC X Y u u' vR i0 i0' νq κ :=
    ptValueC_of X Y u u' vR i0 i0' νq κ (RealDecompL.liftAtSomeC_of X Y u u' κ hAtS) hCU
      (decompPhaseC_of X Y u u' κ hLD hPT) hDF hGP hFT
      (dFrameMoveC_of X u u' i0 i0' (sDecompC_holds X u) (sDecompC_holds X u') (dFrameMoveHC_holds X u u' i0 i0'))
  exact commonFrameC_of X Y u u' vR i0 i0' νq κ hP (vIndepLiftC_of_at X Y u u' vR i0 i0' νq κ hLD hGP hFT hVA)
    (commonDFrameC_of_exact X Y u u' vR i0 i0' νq κ (commonDFrameExactC_of X Y u u' vR i0 i0' νq κ hP
      (pairDFrameC_of X Y u u' i0 i0' κ (scalarAgreeC_of_scalT X Y u u' κ hSc))))
    (irrelZeroC_of X Y u u' vR i0 i0' νq κ hV hAt)

theorem classFrameOO_all
    (hAtS : ∀ t : Term D u u' (X.Fu u) (Y.what₂ u), t.G ≠ 0 → t.relevant → ∃ w, t.atPt w)
    (hTP : ∀ (t : Term D u u' (X.Fu u) (Y.what₂ u)) (w : Point D.host.E (D.R.rS + 1)), t.atPt w →
      TotPos (Gpt (D.mem u).A.T (D.mem u').A.T w))
    (hCU : Formalism.L2.SG.PairVal.CellPtUnique D u u' (X.Fu u) (Y.what₂ u))
    (hDF : DFrameAtS X u u' i0 i0' 1) (hPT : PhaseTieC X Y u u' κ) (hFT : FormTranspC X Y u u' vR νq κ)
    (hVA : VIndepAtC X u u' i0 i0' νq 1) (hSc : ScalTC X Y u u' κ) (hV : LemmaVLiftC X Y u u' κ)
    (hAt : AtPtRelevantC X Y u u') :
    ClassFrameOO X Y u u' vR i0 i0' νq κ :=
  Formalism.L2.SG.Pf.classFrameOO_of X Y u u' vR i0 i0' νq κ
    (normalFormC_all X Y u u' vR i0 i0' νq κ hAtS hTP hCU hDF hPT hFT)
    (commonFrameC_all X Y u u' vR i0 i0' νq κ hAtS hTP hCU hDF hPT hFT hVA hSc hV hAt) hV hAt

theorem classFrameC_all
    (hAtS : ∀ t : Term D u u' (X.Fu u) (Y.what₂ u), t.G ≠ 0 → t.relevant → ∃ w, t.atPt w)
    (hTP : ∀ (t : Term D u u' (X.Fu u) (Y.what₂ u)) (w : Point D.host.E (D.R.rS + 1)), t.atPt w →
      TotPos (Gpt (D.mem u).A.T (D.mem u').A.T w))
    (hCU : Formalism.L2.SG.PairVal.CellPtUnique D u u' (X.Fu u) (Y.what₂ u))
    (hDF : DFrameAtS X u u' i0 i0' 1) (hPT : PhaseTieC X Y u u' κ) (hFT : FormTranspC X Y u u' vR νq κ)
    (hVA : VIndepAtC X u u' i0 i0' νq 1) (hSc : ScalTC X Y u u' κ) (hV : LemmaVLiftC X Y u u' κ)
    (hAt : AtPtRelevantC X Y u u') (hVol : 0 < X.volK2)
    (hc : 0 ≤ (bCF X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq).c0 *
      (bCF X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq).c0') :
    ClassFrameC X hb Y u u' X0 ψ sd C Th vR Q M δ i0 i0' νq κ :=
  classFrameC_of_OO X hb Y u u' X0 ψ sd C Th vR Q M δ i0 i0' νq κ
    (classFrameOO_all X Y u u' vR i0 i0' νq κ hAtS hTP hCU hDF hPT hFT hVA hSc hV hAt) hVol hc

end Formalism.L2.SG.Pf.RowForm
