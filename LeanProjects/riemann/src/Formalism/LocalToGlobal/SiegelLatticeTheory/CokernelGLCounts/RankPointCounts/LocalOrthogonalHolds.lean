import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FrameMemUUE
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdBetaS

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open BwdCut BwdBetaCut BwdNP BetaI

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

set_option maxHeartbeats 1000000 in

theorem localOrthogonal_holds : PartialIsometryExtension Zd u u' F0 what₂ := by
  intro γ Z F'₂ φ φ' Λ₂ hB β₀ hβ₀ hfr hW0 hOm p w hw hm hm₂
  have hStar := hB.2.2.1
  have hT2 := hStar.2.1 p
  have hId := hT2.2.2.2.1

  have hwW := OrthogonalLocalComplement.baseChange_mem_W0 Zd p γ hw
  obtain ⟨w₂, hw₂, hs1, hs2⟩ := hId.2.2.1 (baseChange₂ D p w) hwW

  have hzrep : (repF γ).zt = (repF γ).fl.z := hB.2.2.2.2.2.2.1.1.2
  have hwHp : w ∈ Hp γ.lam (lf D F0) (repF γ) := by
    have hle := BwdBetaS.UUE_le_span γ.lam (lf D F0) (repF γ) rfl hzrep
    have hspan : Submodule.span D.host.E (Set.range (Sum.elim (lf D F0).fl.fvec (repF γ).fl.fvec)) =
        F0.Xplus ⊔ (repF γ).fl.Xplus := by
      rw [Set.Sum.elim_range, Submodule.span_union, SpanOmPf.Xplus_eq, SpanOmPf.Xplus_eq]
    rw [hspan] at hle
    show w ∈ orth (VS D) (UUE γ.lam (lf D F0) (repF γ))
    rw [PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth] at hw ⊢
    exact fun x hx => hw x (hle hx)
  obtain ⟨w₂g, hw₂g, hd1, hd2⟩ := hW0 w hwHp

  have hu := OrthogonalLocalComplement.hu_all Zd p
  have hwperp : baseChange₂ D p w ∈ (locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f) :=
    baseChange_mem_perp_sup Zd p γ ((PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).2 fun x hx =>
      (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hw x
        (Submodule.mem_sup_left (le_sup_left (a := F0.X) (b := Submodule.span D.host.E {F0.z}) hx)))
  have hw₂perp : w₂ ∈ (locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f) := LsDatumA.mem_perp_isotropicSpan_of_mem_framePerp _ hw₂
  have hdiff1 : baseChange₂ D p w - w₂ ∈ (locH Zd p).X (tLoc Zd p γ).f := by
    have h := hs1 ⟨baseChange₂ D p w, hwperp⟩ ⟨w₂, hw₂perp⟩ rfl rfl
    have h1 : (φ p) ((locH Zd p).mkW (tLoc Zd p γ).f ⟨baseChange₂ D p w, hwperp⟩) =
        (locH Zd p).mkW (tLoc Zd p γ).f ⟨w₂, hw₂perp⟩ := by
      have := h
      simp only [one_smul] at this
      exact this
    have e' : ∀ x, (φ p) x = x := fun x => by rw [hStar.2.2 p]; rfl
    exact LsDatumA.sub_mem_X_of_mkW_eq _ ((e' _).symm.trans h1)
  have hdiff2 : baseChange₂ D p w - baseChange₂ D p w₂g ∈ (locH Zd p).X (tLoc Zd p γ).f := by
    rw [← map_sub]
    exact bcP_X Zd p γ hu hd1
  have hdX : w₂ - baseChange₂ D p w₂g ∈ (locH Zd p).X (tLoc Zd p γ).f := by
    have := Submodule.sub_mem _ hdiff2 hdiff1
    rwa [sub_sub_sub_cancel_left] at this
  have hd0 : ∀ a, (locH Zd p).h (w₂ - baseChange₂ D p w₂g) (locF' Zd p F'₂ a) = 0 := by
    intro a
    have h1 : (locH Zd p).h w₂ (locF' Zd p F'₂ a) = 0 :=
      hw₂ _ (Submodule.mem_sup_right (Submodule.subset_span ⟨a, rfl⟩))
    have h2 : (locH Zd p).h (baseChange₂ D p w₂g) (locF' Zd p F'₂ a) = 0 := by
      rw [h_eq, locF'_eq, LocFacts.localForm_smul_right, ← h_eq, localForm_baseChange,
        (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hw₂g _ (OrthogonalLocalComplement.frame_mem_UUE hB.2.2.2.1.1 (lf D F0) F'₂ a),
        map_zero, mul_zero]
    rw [OmL.h_sub_left, h1, h2, sub_zero]
  have hgen := (hB.2.2.2.1.2 p).1
  have hdet : IsUnit ((locH Zd p).Zhat (locF' Zd p F'₂) (tLoc Zd p γ).f).det := by
    have h := hgen.1.2.2.2.1
    rw [OmL.dl_last] at h
    rw [LsDatumA.Zhat_swap, Matrix.det_transpose, ← RingHom.map_det]
    exact h.map _
  have hd : w₂ - baseChange₂ D p w₂g = 0 :=
    OmL.uniq_loc (locH Zd p) (locF' Zd p F'₂) (tLoc Zd p γ).f hdet
      (le_trans (Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨i.castSucc, rfl⟩)) le_rfl hdX) hd0
  have hw₂eq : w₂ = baseChange₂ D p w₂g := sub_eq_zero.1 hd

  have hw₂perp' : w₂ ∈ (locH Zd p).perp ((locH Zd p).X (locF' Zd p F'₂)) := LsDatumA.mem_perp_isotropicSpan_of_mem_framePerp' _ hw₂
  have h := hs2 ⟨baseChange₂ D p w, hm⟩ ⟨w₂, hw₂perp'⟩ rfl rfl
  have h' : (φ' p) ((locH Zd p).mkW (tLoc Zd p γ).f' ⟨baseChange₂ D p w, hm⟩) =
      (locH Zd p).mkW (locF' Zd p F'₂) ⟨w₂, hw₂perp'⟩ := by
    have := h
    simp only [one_smul] at this
    exact this
  rw [h']
  apply Submodule.Quotient.eq _ |>.2
  show w₂ - baseChange₂ D p (β₀ w) ∈ (locH Zd p).X (locF' Zd p F'₂)
  rw [hw₂eq, ← map_sub, show w₂g - β₀ w = -(β₀ w - w₂g) by abel, map_neg]
  exact Submodule.neg_mem _ (bcP_X' Zd p F'₂ hd2)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
