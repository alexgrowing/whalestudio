import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IotaDictAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqClass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagTermInvariantsConstOnRationalDoubleCoset
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalDataGlobalTermIndependentOfRepresentativeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalTermsSameDoubleCosetSameLocalDataStatement
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermOp NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocOver.TermSame

theorem same : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ t t' : TauC Y u u', t.G ≠ 0 → (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' → Formalism.L2.SG.TermOp.wt t = Formalism.L2.SG.TermOp.wt t' ∧ (nmlOf Y u u' t = nmlOf Y u u' t' → ∀ (p : PlF D) (P : LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), P.RelG (LocNG.theta (Y.M p)) → ∀ d, Over P d (locU (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p t.toTerm.lam (lf D (X.Fu u)) (Quot.out t.toTerm.cls).1 (Tu D u) (Tu D u')) → Over P d (locU (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p t'.toTerm.lam (lf D (X.Fu u)) (Quot.out t'.toTerm.cls).1 (Tu D u) (Tu D u'))) := by
  intro D X Y u u' t t' hG hr
  have hl : t.lam = t'.lam := congrArg (fun r => (r.1 : {Λ // Λ ∈ Y.what₂ u}).1) hr
  have hl' : t.lam' = t'.lam' := congrArg (fun r => (r.2.1 : {Λ // Λ ∈ Y.what₂ u'}).1) hr
  have hi : iotaOf Y.TR (Y.cs u) (Y.cs u') t = iotaOf Y.TR (Y.cs u) (Y.cs u') t' := congrArg (fun r => r.2.2) hr
  refine ⟨by simp only [Formalism.L2.SG.TermOp.wt, hl, hl'], fun hnml p P hP d hO => ?_⟩
  have hΛ : IsRowLat D (X.Fu u) t.lam := (Y.rowsOK u).1 t.lam t.mem
  have hΛ' : IsRowLat D (X.Fu u) t'.lam := (Y.rowsOK u).1 t'.lam t'.mem
  have one_nrat : ∀ {T : D.host.E} (F : LFlag (VS D) D.R.rS T), (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ NRat F := by
    intro T F
    have h := one_mem_NLam (⊤ : Submodule (𝓞 D.host.E) (VS D).V) F
    exact ⟨h.1.1, h.2.1, h.2.2⟩
  have hmem : t'.lin ∈ nmlOf Y u u' t := by
    rw [hnml]
    exact ⟨1, one_nrat _, 1, one_nrat _, by simp⟩
  obtain ⟨n, hn, n', hn', hlin⟩ := hmem
  have h0 : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have h1 : t'.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t'.rep.2.2.1
  have hmN : t.lin * n' * t.lin⁻¹ ∈ NRat t.frame := by
    have h := GlobalTheory.HL.CosetConst.conj_nlam_top (G := lf D (X.Fu u')) h0 hn'
    exact ⟨h.1.1, h.2.1, h.2.2⟩
  have hβ : n * (t.lin * n' * t.lin⁻¹) = t'.lin * t.lin⁻¹ := by
    rw [hlin]; simp only [mul_assoc]
  have hgm : Formalism.HermitianLatticesTheory.gmap (n * (t.lin * n' * t.lin⁻¹)) t.lam = t.lam := by
    have hg0 : Formalism.HermitianLatticesTheory.gmap t.lin t.lam' = t.lam := t.rep.2.2.2.1
    have hg1 : Formalism.HermitianLatticesTheory.gmap t'.lin t'.lam' = t'.lam := t'.rep.2.2.2.1
    rw [hβ, Formalism.L2.SG.Pf.MainEqClass.gmap_mul', Formalism.L2.SG.Pf.MainEqClass.gmap_inv_of' hg0, hl', hg1, hl]
  have hfr : ∀ a, frame t'.frame a = (n * (t.lin * n' * t.lin⁻¹)) (frame t.frame a) := by
    intro a
    rw [hβ]
    show frame (mapLF t'.lin (lf D (X.Fu u'))) a = (t'.lin * t.lin⁻¹) (frame (mapLF t.lin (lf D (X.Fu u'))) a)
    rw [GlobalTheory.HL.CosetConst.frame_mapLF h1, GlobalTheory.HL.CosetConst.frame_mapLF h0]
    show _ = t'.lin (t.lin.symm (t.lin _))
    rw [LinearEquiv.symm_apply_apply]
  have hI := Formalism.L2.SG.Pf.iotaDict_fwd Y t t' hl hl' hi
  rw [← hβ] at hI
  have hEq := Formalism.L2.SG.Closed.TermEqIff_holds D u u' (X.Fu u) t.lam hΛ
  have hGF := (Formalism.L2.SG.Closed.TermFun_holds D u u' (X.Fu u) t.lam hΛ).1
  have hrel : DCRel t.lam (lf D (X.Fu u)) (Quot.out t.toTerm.cls).1 t.frame :=
    (hEq (Quot.out t.toTerm.cls) ⟨t.frame, t.rep.2.2.2.2⟩).1 (Quot.out_eq _)
  have hR0 : Gval (lf D (X.Fu u)) (Quot.out t.toTerm.cls).1 ≠ 0 := hG
  have hGt : Gval (lf D (X.Fu u)) t.frame ≠ 0 := by
    have e : Gval (lf D (X.Fu u)) (Quot.out t.toTerm.cls).1 = Gval (lf D (X.Fu u)) t.frame :=
      hGF (Quot.out t.toTerm.cls) ⟨t.frame, t.rep.2.2.2.2⟩ hrel
    rw [← e]; exact hR0
  have hGt' : Gval (lf D (X.Fu u)) t'.frame ≠ 0 := by
    have hh : t'.lin = n⁻¹⁻¹ * t.lin * n' := by rw [inv_inv]; exact hlin
    rw [← GlobalTheory.HL.CosetConst.G_eq_frames t t' (Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_inv _ hn) hn' hh]
    exact hGt
  have s1 := (GlobalTheory.T.localData_globalTerm_independent_of_representative D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) u u' (X.Fu u) t.lam hΛ
    (Quot.out t.toTerm.cls).1 t.frame (Quot.out t.toTerm.cls).2 t.rep.2.2.2.2 hR0 hrel p P hP d).1 hO
  have hpd' : PD D t.lam (lf D (X.Fu u)) u' t'.frame := by rw [hl]; exact t'.rep.2.2.2.2
  have s2 := GlobalTheory.T.global_terms_same_doubleCoset_same_local_data D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) u u' (X.Fu u) t.lam hΛ t.frame t'.frame
    t.rep.2.2.2.2 hpd' hGt n hn _ hmN hgm hfr hI p P hP d s1
  have s3 : Over P d (locU (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p t'.lam (lf D (X.Fu u)) t'.frame (Tu D u) (Tu D u')) := by
    rw [← hl]; exact s2
  have hEq' := Formalism.L2.SG.Closed.TermEqIff_holds D u u' (X.Fu u) t'.lam hΛ'
  have hrel' : DCRel t'.lam (lf D (X.Fu u)) t'.frame (Quot.out t'.toTerm.cls).1 :=
    (hEq' ⟨t'.frame, t'.rep.2.2.2.2⟩ (Quot.out t'.toTerm.cls)).1 (Quot.out_eq _).symm
  exact (GlobalTheory.T.localData_globalTerm_independent_of_representative D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) u u' (X.Fu u) t'.lam hΛ' t'.frame
    (Quot.out t'.toTerm.cls).1 t'.rep.2.2.2.2 (Quot.out t'.toTerm.cls).2 hGt' hrel' p P hP d).1 s3

end GlobalTheory.LocOver.TermSame
