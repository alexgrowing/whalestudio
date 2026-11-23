import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaRatA
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdBetaK
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarOmLocPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarGlob

noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated
  Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

open BwdCut BwdBetaCut OmP BwdBetaS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)

set_option maxHeartbeats 1000000 in

theorem betaRat_holds : BetaRat Zd u u' F0 what₂ := by
  intro γ Z F'₂ φ φ' Λ₂ hB
  obtain ⟨hC, hCtx, hS, -, -, hTH, hPD, hGv⟩ := hB
  obtain ⟨hZd, hZ₁d', hx'⟩ := starMinors_holds u u' F0 what₂ γ Z hCtx
  have hZ : ZhatL (lf D F0) F'₂ = Z := hS.1
  have hrow := hC.2.1.1 γ.lam γ.mem
  have hΛ : Submodule.IsLattice D.host.E γ.lam := hrow.2.1.1
  have hLlf : IsLift γ.lam (lf D F0) := hrow.2.1.2.2.1
  have hLrep : IsLift γ.lam (repF γ) := hPD.1
  set f := frame (lf D F0) with hf
  set g := frame (repF γ) with hg
  set F₂ := F'₂.fl with hF₂
  set Z₁ := starZh f g with hZ₁
  have hlm : ∀ l, leadMinorE Z₁ l = leadMinorE (starZh f (starFrame γ)) l := fun l => (star_frame_lead_minor γ l).symm
  have hZ₁d : Z₁.det ≠ 0 := by
    rw [← FsLA.leadMinorE_full, hlm, FsLA.leadMinorE_full]; exact hZ₁d'
  have hx : leadMinorE Z₁ D.R.rS * Z.det = leadMinorE Z D.R.rS * Z₁.det := by
    rw [hlm, ← FsLA.leadMinorE_full Z₁, hlm, FsLA.leadMinorE_full]; exact hx'
  have hfF : f = F0.fvec := rfl
  have hZe : ∀ a b, (VS D).hT (f a) (F₂.fvec b) = Z a b := fun a b => by rw [← hZ]; rfl
  have hg2 : FsLA.gram (VS D) f F₂.fvec = Zᴴ := by
    refine Matrix.ext fun i j => ?_
    simp only [FsLA.gram, Matrix.conjTranspose_apply]
    rw [← hZe, ← (LinearMap.isSymm_def.1 (VS D).herm) (f j) (F₂.fvec i), starRingEnd_apply]
  have h1g : ∀ a b, (a ≠ Fin.last D.R.rS ∨ b ≠ Fin.last D.R.rS) → (VS D).hT (g a) (g b) = 0 :=
    fun a b h => FsLA.gram_fvec_zero (repF γ).fl a b h
  have h2g : (VS D).hT (g (Fin.last D.R.rS)) (g (Fin.last D.R.rS)) = -((Tu D u' : ℕ) : D.host.E) :=
    FsLA.gram_fvec_last (repF γ).fl
  have h1f : ∀ a b, (a ≠ Fin.last D.R.rS ∨ b ≠ Fin.last D.R.rS) → (VS D).hT (f a) (f b) = 0 :=
    fun a b h => FsLA.gram_fvec_zero F0 a b h
  have h2f : (VS D).hT (f (Fin.last D.R.rS)) (f (Fin.last D.R.rS)) = -CntLocal.Tn u := FsLA.gram_fvec_last F0
  have hdZ1h : Z₁ᴴ.det ≠ 0 := by rw [Matrix.det_conjTranspose]; exact star_ne_zero.2 hZ₁d
  have hdg2 : (FsLA.gram (VS D) f F₂.fvec).det ≠ 0 := by
    rw [hg2, Matrix.det_conjTranspose]; exact star_ne_zero.2 hZd
  have hx2 : leadMinorE (FsLA.gram (VS D) f F₂.fvec) D.R.rS * Z₁ᴴ.det =
      leadMinorE Z₁ᴴ D.R.rS * (FsLA.gram (VS D) f F₂.fvec).det := by
    rw [hg2, FsLA.lm_conjTranspose, FsLA.lm_conjTranspose, Matrix.det_conjTranspose, Matrix.det_conjTranspose,
      ← star_mul', ← star_mul', mul_comm (leadMinorE Z D.R.rS), hx, mul_comm]
  obtain ⟨F₃, hZ3, hom3, hsp3⟩ := FsLA.frame_la F₂ f h1f h2f Z₁ᴴ hdZ1h hdg2 hx2
  set h := F₃.fvec with hh
  set uu := Sum.elim f g with huu
  set uu' := Sum.elim h F₂.fvec with huu'
  set ww := Sum.elim f F₂.fvec with hww
  have hZ3e : ∀ a b, (VS D).hT (F₂.fvec a) (h b) = Z₁ᴴ a b := fun a b => congrFun (congrFun hZ3 a) b
  have k1 : ∀ a b, (VS D).hT (h a) (h b) = (VS D).hT (f a) (f b) := by
    intro a b
    by_cases hab : a ≠ Fin.last D.R.rS ∨ b ≠ Fin.last D.R.rS
    · exact (FsLA.gram_fvec_zero F₃ a b hab).trans (FsLA.gram_fvec_zero F0 a b hab).symm
    · push_neg at hab
      rw [hab.1, hab.2]
      exact (FsLA.gram_fvec_last F₃).trans (FsLA.gram_fvec_last F0).symm
  have k2 : ∀ a b, (VS D).hT (h a) (F₂.fvec b) = (VS D).hT (f a) (g b) := by
    intro a b
    rw [← (LinearMap.isSymm_def.1 (VS D).herm) (F₂.fvec b) (h a), hZ3e, starRingEnd_apply,
      Matrix.conjTranspose_apply, star_star]
    rfl
  have k3 : ∀ a b, (VS D).hT (F₂.fvec a) (h b) = (VS D).hT (g a) (f b) := by
    intro a b
    rw [hZ3e, Matrix.conjTranspose_apply, ← starRingEnd_apply]
    exact (LinearMap.isSymm_def.1 (VS D).herm) (f b) (g a)
  have k4 : ∀ a b, (VS D).hT (F₂.fvec a) (F₂.fvec b) = (VS D).hT (g a) (g b) := by
    intro a b
    by_cases hab : a ≠ Fin.last D.R.rS ∨ b ≠ Fin.last D.R.rS
    · exact (FsLA.gram_fvec_zero F₂ a b hab).trans (h1g a b hab).symm
    · push_neg at hab
      rw [hab.1, hab.2]
      exact (FsLA.gram_fvec_last F₂).trans h2g.symm
  have hGr : FsLA.gram (VS D) uu' uu' = FsLA.gram (VS D) uu uu := by
    refine Matrix.ext fun i j => ?_
    rcases i with a | a <;> rcases j with b | b
    · exact k1 a b
    · exact k2 a b
    · exact k3 a b
    · exact k4 a b
  have hGg : (FsLA.gram (VS D) g F0.fvec).det * star (FsLA.gram (VS D) g F0.fvec).det -
      CntLocal.Tn u * ((Tu D u' : ℕ) : D.host.E) *
        (leadMinorE (FsLA.gram (VS D) g F0.fvec) D.R.rS * star (leadMinorE (FsLA.gram (VS D) g F0.fvec) D.R.rS))
        ≠ 0 := by
    rw [← FsLA.leadMinorE_full]; exact hGv
  have hdet : (FsLA.gram (VS D) uu uu).det ≠ 0 := FsLA.gram_pair_det F0 g h1g h2g hZ₁d hGg
  have hGZ : Gflag F0 F₂ ≠ 0 := hTH.1.2.2
  have hGg₂ : (FsLA.gram (VS D) F₂.fvec F0.fvec).det * star (FsLA.gram (VS D) F₂.fvec F0.fvec).det -
      CntLocal.Tn u * ((Tu D u' : ℕ) : D.host.E) *
        (leadMinorE (FsLA.gram (VS D) F₂.fvec F0.fvec) D.R.rS *
          star (leadMinorE (FsLA.gram (VS D) F₂.fvec F0.fvec) D.R.rS)) ≠ 0 := by
    rw [← FsLA.leadMinorE_full]; exact hGZ
  have hdetZ : (Zhat F0 F₂).det ≠ 0 := by
    have e : Zhat F0 F₂ = Z := hZ
    rw [e]; exact hZd
  have hdetw : (FsLA.gram (VS D) ww ww).det ≠ 0 :=
    FsLA.gram_pair_det F0 F₂.fvec (fun a b hab => FsLA.gram_fvec_zero F₂ a b hab) (FsLA.gram_fvec_last F₂)
      hdetZ hGg₂
  have hsp : ∀ i, uu' i ∈ Submodule.span D.host.E (Set.range ww) := by
    have hsub : Set.range (Sum.elim F₂.fvec f) ⊆ Submodule.span D.host.E (Set.range ww) := by
      rintro _ ⟨k, rfl⟩
      rcases k with b | a
      · exact Submodule.subset_span ⟨Sum.inr b, rfl⟩
      · exact Submodule.subset_span ⟨Sum.inl a, rfl⟩
    intro i
    rcases i with a | b
    · exact Submodule.span_le.2 hsub (hsp3 a)
    · exact Submodule.subset_span ⟨Sum.inr b, rfl⟩

  have hdetγ : (Zhat F0 (repF γ).fl).det ≠ 0 := hZ₁d
  obtain ⟨Ω₂, hΩ₂⟩ := exists_om F0 F₂ hdetZ
  obtain ⟨Ωγ, hΩγ⟩ := exists_om F0 (repF γ).fl hdetγ
  have hΩd : Ω₂ - Ωγ ∈ Xsp (lf D F0) :=
    omega_local_holds Zd u u' F0 what₂ hC.2.1 γ Z hCtx F'₂ φ φ' hS hdetγ hZd Ω₂ Ωγ hΩ₂ hΩγ

  have hXq : ∀ y, (∀ k, (VS D).hT (uu k) y = 0) → FsLA.lin ww (FsLA.pc ww y) ∈ F0.X := by
    intro y hy
    have hrem := fun z hz => (FsLA.hT_span_rem ww hdetw y z hz).1
    have hyU : ∀ z ∈ Submodule.span D.host.E (Set.range uu), (VS D).hT z y = 0 :=
      NMoveP.spanL (VS D) uu y hy
    refine BRat.key_X F0 F₂ hdetZ hΩ₂ hGZ (FsLA.lin_sub ww _) (fun a => ?_) ?_
    · have e := hrem (f a) (Submodule.subset_span ⟨Sum.inl a, rfl⟩)
      rw [map_sub, sub_eq_zero] at e
      rw [← e]
      exact hy (Sum.inl a)
    · have e := hrem Ω₂ (Submodule.span_mono (Set.range_comp_subset_range Sum.inr ww) hΩ₂.1)
      rw [map_sub, sub_eq_zero] at e
      rw [← e]
      have e2 : Ω₂ = Ωγ + (Ω₂ - Ωγ) := by abel
      rw [e2, map_add, LinearMap.add_apply]
      have h1 : (VS D).hT Ωγ y = 0 :=
        hyU _ (Submodule.span_mono (Set.range_comp_subset_range Sum.inr uu) hΩγ.1)
      have hXu : ∀ x ∈ Xsp (lf D F0), x ∈ Submodule.span D.host.E (Set.range uu) := by
        intro x hx
        refine Submodule.span_le.2 ?_ hx
        rintro _ ⟨i, rfl⟩
        exact Submodule.subset_span ⟨Sum.inl i.castSucc, by simp [huu, hf, frame, FlagG.fvec]⟩
      rw [h1, hyU _ (hXu _ hΩd), add_zero]
  have hkey : ∀ y y', (∀ k, (VS D).hT (uu k) y = 0) → (∀ k, (VS D).hT (uu k) y' = 0) →
      (VS D).hT (FsLA.lin ww (FsLA.pc ww y)) (FsLA.lin ww (FsLA.pc ww y')) = 0 :=
    fun y y' hy hy' => NMoveP.hT_X_X F0 (hXq y hy) (hXq y' hy')
  obtain ⟨β, hiso, hβu, hβy⟩ := BRat.isometry_extension_two uu uu' ww hGr hdet hdetw hsp hkey
  refine ⟨β, hiso, fun b => hβu (Sum.inr b), fun w0 hw0 => ?_, ?_⟩
  ·
    have hw0u : ∀ k, (VS D).hT (uu k) w0 = 0 := fun k =>
      (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hw0 _
        (PI.PairCorankPos.W.frame_mem_UUE γ.lam hΛ (lf D F0) (repF γ) hLlf hLrep k)
    refine ⟨β w0, ?_, ?_, by rw [sub_self]; exact zero_mem _⟩
    · refine (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).2 fun x hx => ?_
      have hxw : x ∈ Submodule.span D.host.E (Set.range ww) :=
        UUE_le_span Λ₂ (lf D F0) (liftF F'₂) rfl rfl hx
      rw [hβy w0 hw0u]
      exact (FsLA.hT_span_rem ww hdetw w0 x hxw).1
    · rw [hβy w0 hw0u, sub_sub_cancel]
      exact hXq w0 hw0u
  ·
    have homf : FsLA.om (VS D) F₂.fvec f = starOmL f (frame F'₂) := by
      rw [FsLA.om, hg2, ← Matrix.adjugate_conjTranspose]
      simp only [starOmL, Matrix.conjTranspose_apply]
      rw [← hZ]
      rfl
    have homh : FsLA.om (VS D) F₂.fvec h = β (starOmL f g) := by
      simp only [FsLA.om, starOmL, map_sum, map_smul]
      have e : FsLA.gram (VS D) h F₂.fvec = Z₁ᴴ := hZ3
      rw [e]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Matrix.adjugate_conjTranspose, Matrix.conjTranspose_apply]
      congr 1
      exact (hβu (Sum.inl a)).symm
    have e1 : Z₁ᴴ.det = star Z₁.det := Matrix.det_conjTranspose _
    have e2 : (FsLA.gram (VS D) f F₂.fvec).det = star Z.det := by rw [hg2, Matrix.det_conjTranspose]
    rw [e1, e2, homf, homh] at hom3
    have hD1 : GDl (frame (lf D F0)) (frame (repF γ)) (D.R.rS + 1) = Z₁.det := by rw [GDl_top']; rfl
    have hD2 : GDl (frame (lf D F0)) (frame (liftF F'₂)) (D.R.rS + 1) = Z.det := by
      rw [GDl_top']; rw [← hZ]; rfl
    have hO1 : Gom (frame (lf D F0)) (frame (repF γ)) = starOmL f g := rfl
    have hO2 : Gom (frame (lf D F0)) (frame (liftF F'₂)) = starOmL f (frame F'₂) := rfl
    unfold OmB
    rw [hD1, hD2, hO1, hO2]
    have := (Xsp (liftF F'₂)).neg_mem hom3
    rw [neg_sub] at this
    exact this

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
