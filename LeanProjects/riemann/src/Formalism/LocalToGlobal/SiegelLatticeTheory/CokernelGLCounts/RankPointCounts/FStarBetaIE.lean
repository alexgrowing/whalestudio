import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SendsB
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartialIsometryExtension
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdBetaS
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarMinors
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DetZhatSwapUnit

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open BwdCut BwdBetaCut BwdNP BetaI

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

namespace BetaI

theorem sub_add_eq {R W : Type*} [Ring R] [AddCommGroup W] [Module R W] {P : Submodule R W} {a b c : W}
    (ha : a ∈ P) (hb : b ∈ P) (hc : c ∈ P) (e : c = a + b) : (⟨c, hc⟩ : P) = ⟨a, ha⟩ + ⟨b, hb⟩ := by
  subst e; rfl

theorem sub_smul_eq {R W : Type*} [Ring R] [AddCommGroup W] [Module R W] {P : Submodule R W} {a c : W} (k : R)
    (ha : a ∈ P) (hc : c ∈ P) (e : c = k • a) : (⟨c, hc⟩ : P) = k • ⟨a, ha⟩ := by
  subst e; rfl

section Place

variable (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
  (ψ : (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂))
  (β₀ : (VS D).V ≃ₗ[D.host.E] (VS D).V)

theorem sendsB_add {m₁ m₂ : (VS D).V}
    (h₁ : baseChange₂ D p m₁ ∈ (locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f'))
    (h₂ : baseChange₂ D p m₂ ∈ (locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f'))
    (k₁ : baseChange₂ D p (β₀ m₁) ∈ (locH Zd p).perp ((locH Zd p).X (locF' Zd p F'₂)))
    (k₂ : baseChange₂ D p (β₀ m₂) ∈ (locH Zd p).perp ((locH Zd p).X (locF' Zd p F'₂)))
    (s₁ : SendsB Zd p γ F'₂ ψ β₀ m₁) (s₂ : SendsB Zd p γ F'₂ ψ β₀ m₂) : SendsB Zd p γ F'₂ ψ β₀ (m₁ + m₂) := by
  intro hm hm₂
  have e1 : (⟨baseChange₂ D p (m₁ + m₂), hm⟩ : ↥((locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f'))) =
      ⟨baseChange₂ D p m₁, h₁⟩ + ⟨baseChange₂ D p m₂, h₂⟩ :=
    sub_add_eq h₁ h₂ hm ((baseChange₂ D p).map_add m₁ m₂)
  have e2 : (⟨baseChange₂ D p (β₀ (m₁ + m₂)), hm₂⟩ : ↥((locH Zd p).perp ((locH Zd p).X (locF' Zd p F'₂)))) =
      ⟨baseChange₂ D p (β₀ m₁), k₁⟩ + ⟨baseChange₂ D p (β₀ m₂), k₂⟩ :=
    sub_add_eq k₁ k₂ hm₂ (by rw [LinearEquiv.map_add, (baseChange₂ D p).map_add])
  have f1 : (locH Zd p).mkW (tLoc Zd p γ).f' ⟨baseChange₂ D p (m₁ + m₂), hm⟩ =
      (locH Zd p).mkW (tLoc Zd p γ).f' ⟨baseChange₂ D p m₁, h₁⟩ + (locH Zd p).mkW (tLoc Zd p γ).f' ⟨baseChange₂ D p m₂, h₂⟩ :=
    (congrArg _ e1).trans (LinearMap.map_add _ _ _)
  have f2 : (locH Zd p).mkW (locF' Zd p F'₂) ⟨baseChange₂ D p (β₀ (m₁ + m₂)), hm₂⟩ =
      (locH Zd p).mkW (locF' Zd p F'₂) ⟨baseChange₂ D p (β₀ m₁), k₁⟩ +
        (locH Zd p).mkW (locF' Zd p F'₂) ⟨baseChange₂ D p (β₀ m₂), k₂⟩ :=
    (congrArg _ e2).trans (LinearMap.map_add _ _ _)
  exact ((congrArg ψ f1).trans (LinearEquiv.map_add ψ _ _)).trans
    ((congrArg₂ (· + ·) (s₁ h₁ k₁) (s₂ h₂ k₂)).trans f2.symm)

theorem sendsB_smul (c : D.host.E) {m : (VS D).V}
    (h₁ : baseChange₂ D p m ∈ (locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f'))
    (k₁ : baseChange₂ D p (β₀ m) ∈ (locH Zd p).perp ((locH Zd p).X (locF' Zd p F'₂)))
    (s : SendsB Zd p γ F'₂ ψ β₀ m) : SendsB Zd p γ F'₂ ψ β₀ (c • m) := by
  intro hm hm₂
  have e1 : (⟨baseChange₂ D p (c • m), hm⟩ : ↥((locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f'))) =
      (D.s.atP p).ιE c • ⟨baseChange₂ D p m, h₁⟩ :=
    sub_smul_eq _ h₁ hm (Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂ p c m)
  have e2 : (⟨baseChange₂ D p (β₀ (c • m)), hm₂⟩ : ↥((locH Zd p).perp ((locH Zd p).X (locF' Zd p F'₂)))) =
      (D.s.atP p).ιE c • ⟨baseChange₂ D p (β₀ m), k₁⟩ :=
    sub_smul_eq _ k₁ hm₂ (by rw [LinearEquiv.map_smul]; exact Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂ p c (β₀ m))
  have f1 : (locH Zd p).mkW (tLoc Zd p γ).f' ⟨baseChange₂ D p (c • m), hm⟩ =
      (D.s.atP p).ιE c • (locH Zd p).mkW (tLoc Zd p γ).f' ⟨baseChange₂ D p m, h₁⟩ :=
    (congrArg _ e1).trans (LinearMap.map_smul _ _ _)
  have f2 : (locH Zd p).mkW (locF' Zd p F'₂) ⟨baseChange₂ D p (β₀ (c • m)), hm₂⟩ =
      (D.s.atP p).ιE c • (locH Zd p).mkW (locF' Zd p F'₂) ⟨baseChange₂ D p (β₀ m), k₁⟩ :=
    (congrArg _ e2).trans (LinearMap.map_smul _ _ _)
  exact ((congrArg ψ f1).trans (LinearEquiv.map_smul ψ _ _)).trans
    ((congrArg ((D.s.atP p).ιE c • ·) (s h₁ k₁)).trans f2.symm)

theorem sendsB_X {m : (VS D).V} (hX1 : baseChange₂ D p m ∈ (locH Zd p).X (tLoc Zd p γ).f')
    (hX2 : baseChange₂ D p (β₀ m) ∈ (locH Zd p).X (locF' Zd p F'₂)) : SendsB Zd p γ F'₂ ψ β₀ m := by
  intro hm hm₂
  have e1 : (locH Zd p).mkW (tLoc Zd p γ).f' ⟨baseChange₂ D p m, hm⟩ = 0 := (Submodule.Quotient.mk_eq_zero _).2 hX1
  have e2 : (locH Zd p).mkW (locF' Zd p F'₂) ⟨baseChange₂ D p (β₀ m), hm₂⟩ = 0 := (Submodule.Quotient.mk_eq_zero _).2 hX2
  rw [e1, e2]
  exact LinearEquiv.map_zero ψ

theorem bcP_X_f' {x : (VS D).V} (hx : x ∈ Xsp (repF γ)) : baseChange₂ D p x ∈ (locH Zd p).X (tLoc Zd p γ).f' := by
  obtain ⟨h1, -⟩ := admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)
  set ξ := admXi D γ.lam (lf D F0) (repF γ) with hξdef
  have hξ : ξ⁻¹ * ξ = 1 := OmL.admissibility_witness_inv_mul γ.lam (lf D F0) (repF γ)
  have key : ∀ b, ∑ a, ((ξ a b : 𝓞 D.host.E) : D.host.E) • frameAct (frame (repF γ)) ξ⁻¹ a = frame (repF γ) b := by
    intro b
    simp only [frameAct, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    have h1' : ∀ c, ∑ a, ((ξ a b : 𝓞 D.host.E) : D.host.E) * ((ξ⁻¹ c a : 𝓞 D.host.E) : D.host.E) =
        (((ξ⁻¹ * ξ) c b : 𝓞 D.host.E) : D.host.E) := by
      intro c
      rw [Matrix.mul_apply]
      push_cast
      exact Finset.sum_congr rfl fun a _ => mul_comm _ _
    simp only [← Finset.sum_smul, h1', hξ, Matrix.one_apply]
    simp
  change x ∈ Submodule.span D.host.E (Set.range (repF γ).fl.e) at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    rw [← frame_csG, ← key, map_sum, Fin.sum_univ_castSucc]
    have hl : ξ (Fin.last D.R.rS) j.castSucc = 0 := h1 _ _ (Fin.castSucc_lt_last j)
    rw [hl]
    simp only [Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂]
    refine add_mem (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_) (by simp)
    have e : baseChange₂ D p (frameAct (frame (repF γ)) ξ⁻¹ i.castSucc) =
        (((isUnit_sF' Zd p i.castSucc).unit⁻¹ : ((D.s.atP p).Ep)ˣ) : (D.s.atP p).Ep) • (tLoc Zd p γ).f' i.castSucc := by
      rw [tf', smul_smul]
      have : ((((isUnit_sF' Zd p i.castSucc).unit⁻¹ : ((D.s.atP p).Ep)ˣ)) : (D.s.atP p).Ep) *
          (TermLoc.sgnP' D p i.castSucc * frFac Zd.δ p i.castSucc) = 1 := (isUnit_sF' Zd p i.castSucc).val_inv_mul
      rw [this, one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c x _ hx => rw [Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂]; exact Submodule.smul_mem _ _ hx

end Place

section Place2

variable (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
  (ψ : (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂))
  (β₀ : (VS D).V ≃ₗ[D.host.E] (VS D).V)

theorem z_orthG {T' : D.host.E} (G : LFlag (VS D) D.R.rS T') : G.fl.z ∈ orth (VS D) (Xsp G) :=
  (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).2 fun x hx => by
    rw [BwdNA.hsw (VS D) G.fl.z x]
    have h := NMoveP.hT_f_X G.fl (Fin.last D.R.rS) hx
    rw [NMoveP.fvecL] at h
    rw [h, star_zero]

theorem X_le_orthG {T' : D.host.E} (G : LFlag (VS D) D.R.rS T') : Xsp G ≤ orth (VS D) (Xsp G) :=
  BwdNA.X_le_orth (VS D) (Xsp G) fun _ hx _ hy => NMoveP.hT_X_X G.fl hx hy

theorem starLast_sub_mem :
    frameAct (frame (repF γ)) (admXi D γ.lam (lf D F0) (repF γ))⁻¹ (Fin.last D.R.rS) - (repF γ).fl.z ∈
      Xsp (repF γ) := by
  obtain ⟨-, hξ2⟩ := inv_unitri _ (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).1 (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).2
  show ∑ a, (((admXi D γ.lam (lf D F0) (repF γ))⁻¹ a (Fin.last D.R.rS) : 𝓞 D.host.E) : D.host.E) • frame (repF γ) a -
    (repF γ).fl.z ∈ Xsp (repF γ)
  rw [Fin.sum_univ_castSucc, hξ2, frame_lastG, (by simp : ((1 : 𝓞 D.host.E) : D.host.E) = 1), one_smul,
    add_sub_cancel_right]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
  rw [frame_csG]
  exact Submodule.subset_span ⟨j, rfl⟩

theorem sends_beta_z
    (hS : (locH Zd p).SendsTo ψ.toLinearMap 1 1 ((tLoc Zd p γ).f' (Fin.last D.R.rS)) (locF' Zd p F'₂ (Fin.last D.R.rS)))
    (hzβ : β₀ (repF γ).fl.z = F'₂.fl.z) : SendsB Zd p γ F'₂ ψ β₀ (repF γ).fl.z := by
  intro hm hm₂
  obtain ⟨g, hg⟩ : ∃ g, g = frameAct (frame (repF γ)) (admXi D γ.lam (lf D F0) (repF γ))⁻¹ (Fin.last D.R.rS) :=
    ⟨_, rfl⟩
  have hd : g - (repF γ).fl.z ∈ Xsp (repF γ) := hg ▸ starLast_sub_mem γ
  have hlast : (tLoc Zd p γ).f' (Fin.last D.R.rS) = baseChange₂ D p g := by
    rw [tf', hg]
    have h1 : TermLoc.sgnP' D p (Fin.last D.R.rS) * frFac Zd.δ p (Fin.last D.R.rS) = 1 := sF'_last Zd p
    rw [h1, one_smul]
  have hgo : g ∈ orth (VS D) (Xsp (repF γ)) := by
    have e : g = (repF γ).fl.z + (g - (repF γ).fl.z) := by abel
    rw [e]
    exact add_mem (z_orthG (repF γ)) (X_le_orthG (repF γ) hd)
  have hmem : (tLoc Zd p γ).f' (Fin.last D.R.rS) ∈ (locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f') :=
    hlast ▸ bcP_perp_f' Zd p γ hgo
  have h2 : baseChange₂ D p (β₀ (repF γ).fl.z) = locF' Zd p F'₂ (Fin.last D.R.rS) := by
    rw [hzβ, locF'_last]
  have h3 : (1 : (D.s.atP p).Ep) • ψ.toLinearMap ((locH Zd p).mkW (tLoc Zd p γ).f' ⟨_, hmem⟩) =
      (1 : (D.s.atP p).Ep) • (locH Zd p).mkW (locF' Zd p F'₂) ⟨_, hm₂⟩ :=
    hS ⟨(tLoc Zd p γ).f' (Fin.last D.R.rS), hmem⟩ ⟨baseChange₂ D p (β₀ (repF γ).fl.z), hm₂⟩ rfl h2
  have h3' := ((one_smul _ _).symm.trans h3).trans (one_smul _ _)
  have hX : baseChange₂ D p (repF γ).fl.z - (tLoc Zd p γ).f' (Fin.last D.R.rS) ∈ (locH Zd p).X (tLoc Zd p γ).f' := by
    rw [hlast, ← (baseChange₂ D p).map_sub]
    have : (repF γ).fl.z - g = -(g - (repF γ).fl.z) := by abel
    rw [this]
    exact bcP_X_f' Zd p γ ((Xsp (repF γ)).neg_mem hd)
  have h4 : (locH Zd p).mkW (tLoc Zd p γ).f' ⟨baseChange₂ D p (repF γ).fl.z, hm⟩ =
      (locH Zd p).mkW (tLoc Zd p γ).f' ⟨_, hmem⟩ := (Submodule.Quotient.eq _).2 hX
  exact (congrArg ψ h4).trans h3'

end Place2

end BetaI

theorem pinB_of (hSp : SpanOm D) (hOm : PinOm Zd u u' F0 what₂) (hW0 : PartialIsometryExtension Zd u u' F0 what₂) :
    PinB Zd u u' F0 what₂ := by
  intro γ Z F'₂ φ φ' Λ₂ hB β₀ hiso hfr hW hO p m hm hm₂ hmo
  have hB0 := hB
  obtain ⟨-, hZ, hSt, -, -, -, -, hG⟩ := hB
  obtain ⟨-, hZ₁d, -⟩ := starMinors_holds u u' F0 what₂ γ Z hZ
  have hl1 := star_frame_lead_minor γ (D.R.rS + 1)
  rw [FsLA.leadMinorE_full, FsLA.leadMinorE_full] at hl1
  have hdet1 : (Zhat F0 (repF γ).fl).det ≠ 0 := fun h0 => hZ₁d (hl1.trans h0)
  have hzβ : β₀ (repF γ).fl.z = F'₂.fl.z := by
    have := hfr (Fin.last _)
    rwa [BwdBetaCut.fvec_last', BwdBetaCut.fvec_last'] at this
  have hXmap := BwdBetaCut.Xsp_of_frame β₀ _ _ hfr
  have horth : ∀ y ∈ orth (VS D) (Xsp (repF γ)), β₀ y ∈ orth (VS D) (Xsp (liftF F'₂)) := by
    intro y hy
    rw [← hXmap, Formalism.L2.SG.Pf.orth_map_sat β₀ hiso]
    exact Submodule.mem_map_of_mem hy
  have hmapX : ∀ x ∈ Xsp (repF γ), β₀ x ∈ Xsp (liftF F'₂) := fun x hx => by
    rw [← hXmap]; exact Submodule.mem_map_of_mem hx
  have k1 : ∀ y, y ∈ orth (VS D) (Xsp (repF γ)) →
      baseChange₂ D p y ∈ (locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f') := fun y hy => bcP_perp_f' Zd p γ hy
  have k2 : ∀ y, y ∈ orth (VS D) (Xsp (repF γ)) →
      baseChange₂ D p (β₀ y) ∈ (locH Zd p).perp ((locH Zd p).X (locF' Zd p F'₂)) :=
    fun y hy => baseChangeAt_perp' Zd p F'₂ (horth y hy)
  have hsp := hSp F0 (repF γ).fl hdet1 hG m hmo
  refine Exists.elim hsp fun x' h1 => ?_
  refine Exists.elim h1.2 fun w h2 => ?_
  refine Exists.elim h2.2 fun a h3 => ?_
  refine Exists.elim h3 fun b hmeq => ?_
  have hx' : x' ∈ (repF γ).fl.X := h1.1
  have hw : w ∈ orth (VS D) (F0.Xplus ⊔ (repF γ).fl.Xplus) := h2.1
  subst hmeq
  have ox : x' ∈ orth (VS D) (Xsp (repF γ)) := X_le_orthG (repF γ) hx'
  have hXle : (repF γ).fl.X ≤ F0.Xplus ⊔ (repF γ).fl.Xplus :=
    (show (repF γ).fl.X ≤ (repF γ).fl.Xplus from le_sup_left).trans le_sup_right
  have ow : w ∈ orth (VS D) (Xsp (repF γ)) := (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).2 fun x hx =>
    (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hw x (hXle hx)
  have oz : (repF γ).fl.z ∈ orth (VS D) (Xsp (repF γ)) := z_orthG (repF γ)
  have oo : Gom F0.fvec (repF γ).fl.fvec ∈ orth (VS D) (Xsp (repF γ)) := BwdBetaCut.Gom_orth (lf D F0) (repF γ)
  have sx : SendsB Zd p γ F'₂ (φ' p) β₀ x' :=
    sendsB_X Zd p γ F'₂ (φ' p) β₀ (bcP_X_f' Zd p γ hx') (bcP_X' Zd p F'₂ (hmapX x' hx'))
  have sw : SendsB Zd p γ F'₂ (φ' p) β₀ w := hW0 γ Z F'₂ φ φ' Λ₂ hB0 β₀ hiso hfr hW hO p w hw
  have sz : SendsB Zd p γ F'₂ (φ' p) β₀ (repF γ).fl.z :=
    sends_beta_z Zd p γ F'₂ (φ' p) β₀ (hSt.2.1 p).2.2.2.2.2 hzβ
  have so : SendsB Zd p γ F'₂ (φ' p) β₀ (Gom F0.fvec (repF γ).fl.fvec) := hOm γ Z F'₂ φ φ' Λ₂ hB0 β₀ hiso hfr hW hO p
  have oxw := add_mem ox ow
  have oaz := Submodule.smul_mem _ a oz
  have obo := Submodule.smul_mem _ b oo
  have s1 := sendsB_add Zd p γ F'₂ (φ' p) β₀ (k1 _ ox) (k1 _ ow) (k2 _ ox) (k2 _ ow) sx sw
  have s2 := sendsB_add Zd p γ F'₂ (φ' p) β₀ (k1 _ oxw) (k1 _ oaz) (k2 _ oxw) (k2 _ oaz) s1
    (sendsB_smul Zd p γ F'₂ (φ' p) β₀ a (k1 _ oz) (k2 _ oz) sz)
  have s3 := sendsB_add Zd p γ F'₂ (φ' p) β₀ (k1 _ (add_mem oxw oaz)) (k1 _ obo) (k2 _ (add_mem oxw oaz))
    (k2 _ obo) s2 (sendsB_smul Zd p γ F'₂ (φ' p) β₀ b (k1 _ oo) (k2 _ oo) so)
  exact s3 hm hm₂

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
