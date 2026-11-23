import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaIIotaB

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open BwdCut BwdBetaCut BwdNP BetaI IotaBP

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

namespace IotaBP

theorem isLattice_NgX {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Submodule.IsLattice D.host.E Λ) {T T' : D.host.E}
    (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') : Submodule.IsLattice D.host.E (NgX Λ (gS D) F F') := by
  have hle : NgX Λ (gS D) F F' ≤ Λ := by
    refine sup_le (sup_le ?_ inf_le_left) inf_le_left
    exact Submodule.smul_le_right
  refine ⟨hΛ.fg.of_le hle, ?_⟩
  rw [eq_top_iff, ← hΛ.span_eq_top, Submodule.span_le]
  intro v hv
  have h0 : ((gS D : ℕ) : D.host.E) ≠ 0 := Formalism.L2.SG.Pf.StabIntSh.gS_ne
  have hm : ((gS D : ℕ) : 𝓞 D.host.E) • v ∈ NgX Λ (gS D) F F' :=
    Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hv))
  have e : v = (((gS D : ℕ) : D.host.E))⁻¹ • (((gS D : ℕ) : 𝓞 D.host.E) • v) := by
    rw [← algebraMap_smul D.host.E ((gS D : ℕ) : 𝓞 D.host.E) v, map_natCast, smul_smul, inv_mul_cancel₀ h0, one_smul]
  rw [SetLike.mem_coe, e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hm)

theorem NgX_dec {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T T' : D.host.E} {F : LFlag (VS D) D.R.rS T}
    {F' : LFlag (VS D) D.R.rS T'} {x : (VS D).V} (hx : x ∈ NgX Λ (gS D) F F') :
    ∃ l ∈ Λ, ∃ ξ ∈ XLam Λ F, ∃ ξ' ∈ XLam Λ F', x = ((gS D : ℕ) : D.host.E) • l + ξ + ξ' := by
  obtain ⟨a, ha, ξ', hξ', rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨b, hb, ξ, hξ, rfl⟩ := Submodule.mem_sup.1 ha
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hb
  obtain ⟨l, hl, rfl⟩ := hb
  refine ⟨l, hl, ξ, hξ, ξ', hξ', ?_⟩
  rw [← algebraMap_smul D.host.E ((gS D : ℕ) : 𝓞 D.host.E) l, map_natCast]

theorem representative_admissible_one (hC : CtxP u u' F0 what₂) {γ : TermDef.Term D u u' F0 what₂} {Z : PairVal.MatR D} (hZ : Ctx γ Z) :
    AdmWit γ.lam (gS D) (lf D F0) (repF γ) 1 := by
  obtain ⟨w, hγ, -⟩ := hZ
  have hN := normRepExists_ctx hC
  obtain ⟨⟨hgen, hG⟩, hat⟩ := hγ
  obtain ⟨y, hy⟩ := hN γ w hat (eligRel_holds γ w ⟨⟨hgen, hG⟩, hat⟩) hgen
  have hex : ∃ x : Point D.host.E (D.R.rS + 1) × LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) × PairVal.MatR D ×
      PairVal.MatR D, PairVal.NormRep γ x.1 x.2.1 x.2.2.1 x.2.2.2 := ⟨(w, y), hy⟩
  have hn : nrep γ = some hex.choose := dif_pos hex
  have hrep : repF γ = hex.choose.2.1 := by unfold repF; rw [hn]
  rw [hrep]
  exact hex.choose_spec.2.1

abbrev t2 (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V) : Loc.Term (Vp D p) (Zd.M p) D.R.rS :=
  ⟨lattice₂ D Zd.M p Λ₂, (tLoc Zd p γ).f, locF' Zd p F'₂, (tLoc Zd p γ).T, (tLoc Zd p γ).T'⟩

set_option maxHeartbeats 1000000 in

theorem fwd_typed (p : PlF D) (g : Loc.SplitG (Zd.M p).L) (hsp : (Zd.M p).split = some g)
    (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V)
    (φ' : (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂))
    (hR : Prod.map φ' (LinearEquiv.refl (D.s.atP p).Ep ((locH Zd p).Wb (tLoc Zd p γ).f)) ''
      (locH Zd p).iotaGraph g (tLoc Zd p γ) = (locH Zd p).iotaGraph g (t2 Zd p γ F'₂ Λ₂))
    (β₀ β : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hPin : ∀ (m : (VS D).V) (hm : baseChange₂ D p m ∈ (locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f'))
      (hm₂ : baseChange₂ D p (β₀ m) ∈ (locH Zd p).perp ((locH Zd p).X (locF' Zd p F'₂))),
      m ∈ orth (VS D) (Xsp (repF γ)) →
      φ' ((locH Zd p).mkW (tLoc Zd p γ).f' ⟨baseChange₂ D p m, hm⟩) = (locH Zd p).mkW (locF' Zd p F'₂) ⟨baseChange₂ D p (β₀ m), hm₂⟩)
    (hβ₀o : ∀ m ∈ orth (VS D) (Xsp (repF γ)), β₀ m ∈ orth (VS D) (Xsp (liftF F'₂)))
    (hβo : ∀ m ∈ orth (VS D) (Xsp (repF γ)), β m ∈ orth (VS D) (Xsp (liftF F'₂)))
    (hβd : ∀ m ∈ orth (VS D) (Xsp (repF γ)), β₀ m - β m ∈ Xsp (liftF F'₂))
    (hβX : ∀ y ∈ Xsp (repF γ), β y ∈ Xsp (liftF F'₂)) (hβΛ : ∀ y ∈ γ.lam, β y ∈ Λ₂)
    (hu : ∀ a, IsUnit (TermLoc.sgnP D p a * frFac Zd.δ p a))
    (hXo : Xsp (lf D F0) ≤ orth (VS D) (Xsp (lf D F0))) (hXo' : Xsp (repF γ) ≤ orth (VS D) (Xsp (repF γ)))
    (hA2 : ∀ w ∈ lattice₂ D Zd.M p Λ₂, w ∈ (locH Zd p).X (tLoc Zd p γ).f → w ∈ lattice₂ D Zd.M p (XLam Λ₂ (lf D F0)))
    (hB2 : ∀ w ∈ lattice₂ D Zd.M p Λ₂, w ∈ (locH Zd p).X (locF' Zd p F'₂) →
      w ∈ lattice₂ D Zd.M p (XLam Λ₂ (liftF F'₂)))
    {x' l l₂ μ ξ ξ' : (VS D).V} (hx'Λ : x' ∈ γ.lam) (hx'o : x' ∈ orth (VS D) (Xsp (repF γ))) (hlΛ : l ∈ γ.lam)
    (hlo : l ∈ orth (VS D) (Xsp (lf D F0))) (hl₂Λ : l₂ ∈ Λ₂) (hl₂o : l₂ ∈ orth (VS D) (Xsp (lf D F0)))
    (hll₂ : l - l₂ ∈ Xsp (lf D F0)) (hμ : μ ∈ γ.lam) (hξ : ξ ∈ XLam γ.lam (lf D F0)) (hξ' : ξ' ∈ XLam γ.lam (repF γ))
    (heq : l - x' = ((gS D : ℕ) : D.host.E) • μ + ξ + ξ') :
    baseChange₂ D p (l₂ - β x') ∈ lattice₂ D Zd.M p (NgX Λ₂ (gS D) (lf D F0) (liftF F'₂)) := by
  have hξX : ξ ∈ Xsp (lf D F0) := (Submodule.mem_inf.1 hξ).2
  have hξ'X : ξ' ∈ Xsp (repF γ) := (Submodule.mem_inf.1 hξ').2
  have hm : x' + ξ' ∈ orth (VS D) (Xsp (repF γ)) := add_mem hx'o (hXo' hξ'X)
  have hp1 := BwdNP.baseChange_mem_perp_sup Zd p γ (sub_mem hlo (hXo hξX))
  have hp2 := BetaI.bcP_perp_f' Zd p γ hm
  have hG1 := g1 Zd p (lf D F0) (repF γ) (tLoc Zd p γ) rfl g hsp hlΛ hx'Λ hμ hξ hξ' heq hp1 hp2
  have hm₂ := BetaI.baseChangeAt_perp' Zd p F'₂ (hβ₀o _ hm)
  have hq₂ := BetaI.baseChangeAt_perp' Zd p F'₂ (hβo _ hm)
  have hp₂ := BwdNP.baseChange_mem_perp_sup Zd p γ hl₂o
  have e1 : φ' ((locH Zd p).mkW (tLoc Zd p γ).f' ⟨baseChange₂ D p (x' + ξ'), hp2⟩) =
      (locH Zd p).mkW (locF' Zd p F'₂) ⟨baseChange₂ D p (β (x' + ξ')), hq₂⟩ := by
    rw [hPin (x' + ξ') hp2 hm₂ hm]
    refine (Submodule.Quotient.eq _).2 ?_
    show baseChange₂ D p (β₀ (x' + ξ')) - baseChange₂ D p (β (x' + ξ')) ∈ (locH Zd p).X (locF' Zd p F'₂)
    rw [← map_sub]
    exact BetaI.bcP_X' Zd p F'₂ (hβd _ hm)
  have e2 : (locH Zd p).mkW (tLoc Zd p γ).f ⟨baseChange₂ D p (l - ξ), hp1⟩ =
      (locH Zd p).mkW (tLoc Zd p γ).f ⟨baseChange₂ D p l₂, hp₂⟩ := by
    refine (Submodule.Quotient.eq _).2 ?_
    show baseChange₂ D p (l - ξ) - baseChange₂ D p l₂ ∈ (locH Zd p).X (tLoc Zd p γ).f
    rw [← map_sub]
    refine BwdNP.bcP_X Zd p γ hu ?_
    have e : l - ξ - l₂ = (l - l₂) - ξ := by abel
    rw [e]; exact sub_mem hll₂ hξX
  have hG2 := Set.mem_image_of_mem (Prod.map φ' (LinearEquiv.refl (D.s.atP p).Ep ((locH Zd p).Wb (tLoc Zd p γ).f))) hG1
  rw [hR] at hG2
  simp only [Prod.map, LinearEquiv.refl_apply, e1, e2] at hG2
  have hfin := g2 Zd p (lf D F0) (liftF F'₂) (t2 Zd p γ F'₂ Λ₂) rfl g hsp hl₂Λ
    (hβΛ _ (add_mem hx'Λ (xi_mem hξ'))) hp₂ hq₂ hG2 hA2 hB2
  have hβξ : β ξ' ∈ NgX Λ₂ (gS D) (lf D F0) (liftF F'₂) :=
    Submodule.mem_sup_right (Submodule.mem_inf.2 ⟨hβΛ _ (xi_mem hξ'), hβX _ hξ'X⟩)
  have e : l₂ - β x' = (l₂ - β (x' + ξ')) + β ξ' := by rw [map_add]; abel
  rw [e, map_add]
  exact add_mem hfin (Submodule.subset_span ⟨_, hβξ, rfl⟩)

set_option maxHeartbeats 1000000 in

theorem bwd_typed (p : PlF D) (g : Loc.SplitG (Zd.M p).L) (hsp : (Zd.M p).split = some g)
    (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V)
    (φ' : (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂))
    (hR : Prod.map φ' (LinearEquiv.refl (D.s.atP p).Ep ((locH Zd p).Wb (tLoc Zd p γ).f)) ''
      (locH Zd p).iotaGraph g (tLoc Zd p γ) = (locH Zd p).iotaGraph g (t2 Zd p γ F'₂ Λ₂))
    (β₀ β : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hPin : ∀ (m : (VS D).V) (hm : baseChange₂ D p m ∈ (locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f'))
      (hm₂ : baseChange₂ D p (β₀ m) ∈ (locH Zd p).perp ((locH Zd p).X (locF' Zd p F'₂))),
      m ∈ orth (VS D) (Xsp (repF γ)) →
      φ' ((locH Zd p).mkW (tLoc Zd p γ).f' ⟨baseChange₂ D p m, hm⟩) = (locH Zd p).mkW (locF' Zd p F'₂) ⟨baseChange₂ D p (β₀ m), hm₂⟩)
    (hβ₀o : ∀ m ∈ orth (VS D) (Xsp (repF γ)), β₀ m ∈ orth (VS D) (Xsp (liftF F'₂)))
    (hβo : ∀ m ∈ orth (VS D) (Xsp (repF γ)), β m ∈ orth (VS D) (Xsp (liftF F'₂)))
    (hβd : ∀ m ∈ orth (VS D) (Xsp (repF γ)), β₀ m - β m ∈ Xsp (liftF F'₂)) (hβΛ : ∀ y ∈ γ.lam, β y ∈ Λ₂)
    (hu : ∀ a, IsUnit (TermLoc.sgnP D p a * frFac Zd.δ p a))
    (hXo : Xsp (lf D F0) ≤ orth (VS D) (Xsp (lf D F0)))
    (hXo₂ : Xsp (liftF F'₂) ≤ orth (VS D) (Xsp (liftF F'₂)))
    (hA1 : ∀ w ∈ lattice₂ D Zd.M p γ.lam, w ∈ (locH Zd p).X (tLoc Zd p γ).f → w ∈ lattice₂ D Zd.M p (XLam γ.lam (lf D F0)))
    (hB1 : ∀ w ∈ lattice₂ D Zd.M p γ.lam, w ∈ (locH Zd p).X (tLoc Zd p γ).f' →
      w ∈ lattice₂ D Zd.M p (XLam γ.lam (repF γ)))
    {x' l l₂ μ ξ ξ' : (VS D).V} (hx'Λ : x' ∈ γ.lam) (hx'o : x' ∈ orth (VS D) (Xsp (repF γ))) (hlΛ : l ∈ γ.lam)
    (hlo : l ∈ orth (VS D) (Xsp (lf D F0))) (hl₂Λ : l₂ ∈ Λ₂) (hl₂o : l₂ ∈ orth (VS D) (Xsp (lf D F0)))
    (hll₂ : l - l₂ ∈ Xsp (lf D F0)) (hμ : μ ∈ Λ₂) (hξ : ξ ∈ XLam Λ₂ (lf D F0)) (hξ' : ξ' ∈ XLam Λ₂ (liftF F'₂))
    (heq : l₂ - β x' = ((gS D : ℕ) : D.host.E) • μ + ξ + ξ') :
    baseChange₂ D p (l - x') ∈ lattice₂ D Zd.M p (NgX γ.lam (gS D) (lf D F0) (repF γ)) := by
  have hξX : ξ ∈ Xsp (lf D F0) := (Submodule.mem_inf.1 hξ).2
  have hξ'X : ξ' ∈ Xsp (liftF F'₂) := (Submodule.mem_inf.1 hξ').2
  have hp1 := BwdNP.baseChange_mem_perp_sup Zd p γ (sub_mem hl₂o (hXo hξX))
  have hp2 := BetaI.baseChangeAt_perp' Zd p F'₂ (add_mem (hβo _ hx'o) (hXo₂ hξ'X))
  have hG1 := g1 Zd p (lf D F0) (liftF F'₂) (t2 Zd p γ F'₂ Λ₂) rfl g hsp hl₂Λ (hβΛ _ hx'Λ) hμ hξ hξ' heq hp1 hp2
  rw [← hR] at hG1
  obtain ⟨⟨a', a⟩, ha, hpair⟩ := hG1
  obtain ⟨ha', haa⟩ := Prod.mk.inj hpair
  have hp₁' := BetaI.bcP_perp_f' Zd p γ hx'o
  have hm₂ := BetaI.baseChangeAt_perp' Zd p F'₂ (hβ₀o _ hx'o)
  have hpl := BwdNP.baseChange_mem_perp_sup Zd p γ hlo
  have ea' : a' = (locH Zd p).mkW (tLoc Zd p γ).f' ⟨baseChange₂ D p x', hp₁'⟩ := by
    apply φ'.injective
    rw [ha', hPin x' hp₁' hm₂ hx'o]
    refine (Submodule.Quotient.eq _).2 ?_
    show baseChange₂ D p (β x' + ξ') - baseChange₂ D p (β₀ x') ∈ (locH Zd p).X (locF' Zd p F'₂)
    rw [← map_sub]
    refine BetaI.bcP_X' Zd p F'₂ ?_
    have e : β x' + ξ' - β₀ x' = ξ' - (β₀ x' - β x') := by abel
    rw [e]; exact sub_mem hξ'X (hβd _ hx'o)
  have ea : a = (locH Zd p).mkW (tLoc Zd p γ).f ⟨baseChange₂ D p l, hpl⟩ := by
    refine (show a = (locH Zd p).mkW (tLoc Zd p γ).f ⟨baseChange₂ D p (l₂ - ξ), hp1⟩ from haa).trans ?_
    refine (Submodule.Quotient.eq _).2 ?_
    show baseChange₂ D p (l₂ - ξ) - baseChange₂ D p l ∈ (locH Zd p).X (tLoc Zd p γ).f
    rw [← map_sub]
    refine BwdNP.bcP_X Zd p γ hu ?_
    have e : l₂ - ξ - l = -((l - l₂) + ξ) := by abel
    rw [e]; exact neg_mem (add_mem hll₂ hξX)
  rw [ea', ea] at ha
  exact g2 Zd p (lf D F0) (repF γ) (tLoc Zd p γ) rfl g hsp hlΛ hx'Λ hpl hp₁' ha hA1 hB1

end IotaBP

set_option maxHeartbeats 1000000 in

theorem iotaB_of (hP : PinB Zd u u' F0 what₂) : IotaB Zd u u' F0 what₂ := by
  intro γ Z F'₂ φ φ' Λ₂ hB β₀ hiso hfr hW hO v hv hvf hvX hgm
  have hB0 := hB
  obtain ⟨hC, hZ, hS, hΛ₂, -, hT, hPD, -⟩ := hB
  obtain ⟨hΛ₂lat, hloc₂⟩ := hΛ₂
  obtain ⟨-, hT2, hφ⟩ := hS
  have hrow := hC.2.1.1 γ.lam γ.mem
  have hfix := hrow.2.1
  have hΛlat : Submodule.IsLattice D.host.E γ.lam := hfix.1
  have hXS1 : XLam γ.lam (lf D F0) = XS D F0 := hrow.2.2
  have hXSx : XLam γ.lam (repF γ) = XS D (repF γ).fl := hPD.2.2.2
  have hXS2' : XLam Λ₂ (liftF F'₂) = XS D (liftF F'₂).fl := hT.2.2.2.2

  have hpr1 : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p γ.lam) (tLoc Zd p γ).f := fun p => (hT2 p).1.1.2.1.1
  have hpr2 : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λ₂) (tLoc Zd p γ).f := fun p => (hloc₂ p).1.1.2.1.1
  have hpr2' : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λ₂) (locF' Zd p F'₂) := fun p => (hloc₂ p).1.1.2.2.1.1
  have hadm1 := IotaBP.representative_admissible_one hC hZ
  have hpr1' : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p γ.lam) (locF' Zd p (repF γ)) := fun p =>
    (genXi_holds Zd hC.2.1 γ (repF γ) p hadm1 hPD.1 (hT2 p).1).1.2.2.1.1
  have hu : ∀ p a, IsUnit (TermLoc.sgnP D p a * frFac Zd.δ p a) := fun p a =>
    unit_of_frame Zd p γ (hT2 p).1.1.2.1 a
  have hXS2 : XLam Λ₂ (lf D F0) = XS D F0 := by
    rw [← hXS1]
    ext x
    simp only [XLam, Submodule.mem_inf]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨memX Zd γ hpr2 hpr1 hΛlat hu h2 h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨memX Zd γ hpr1 hpr2 hΛ₂lat hu h2 h1, h2⟩

  have hXmap : (Xsp (repF γ)).map (β₀ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp (liftF F'₂) :=
    BwdBetaCut.Xsp_of_frame β₀ _ _ hfr
  have hvXX : ∀ y ∈ Xsp (liftF F'₂), v y ∈ Xsp (liftF F'₂) := fun y hy => by
    rw [← BwdBetaCut.Xsp_of_frame v (liftF F'₂) (liftF F'₂) hvf]; exact Submodule.mem_map_of_mem hy
  have hβ₀o : ∀ m ∈ orth (VS D) (Xsp (repF γ)), β₀ m ∈ orth (VS D) (Xsp (liftF F'₂)) := fun m hm => by
    rw [← hXmap, Formalism.L2.SG.Pf.orth_map_sat β₀ hiso]; exact Submodule.mem_map_of_mem hm
  have hβX : ∀ y ∈ Xsp (repF γ), (v * β₀) y ∈ Xsp (liftF F'₂) := fun y hy =>
    hvXX _ (by rw [← hXmap]; exact Submodule.mem_map_of_mem hy)
  have hβΛ : ∀ y ∈ γ.lam, (v * β₀) y ∈ Λ₂ := fun y hy => by
    rw [← hgm]; exact (gmap_apply_mem (v * β₀) γ.lam y).2 hy
  have hβo : ∀ m ∈ orth (VS D) (Xsp (repF γ)), (v * β₀) m ∈ orth (VS D) (Xsp (liftF F'₂)) := fun m hm => by
    have h1 := hβ₀o m hm
    have h2 := hvX _ h1
    have e : (v * β₀) m = (v (β₀ m) - β₀ m) + β₀ m := by show v (β₀ m) = _; abel
    rw [e]
    exact add_mem (BwdNA.X_le_orth (VS D) (Xsp (liftF F'₂)) (fun x hx y hy => NMoveP.hT_X_X F'₂.fl hx hy) h2) h1
  have hXo : Xsp (lf D F0) ≤ orth (VS D) (Xsp (lf D F0)) :=
    BwdNA.X_le_orth (VS D) (Xsp (lf D F0)) (fun x hx y hy => NMoveP.hT_X_X F0 hx hy)
  have hXo' : Xsp (repF γ) ≤ orth (VS D) (Xsp (repF γ)) :=
    BwdNA.X_le_orth (VS D) (Xsp (repF γ)) (fun x hx y hy => NMoveP.hT_X_X (repF γ).fl hx hy)

  have hA1 : ∀ p, ∀ w ∈ lattice₂ D Zd.M p γ.lam, w ∈ (locH Zd p).X (tLoc Zd p γ).f →
      w ∈ lattice₂ D Zd.M p (XLam γ.lam (lf D F0)) := fun p w hw hwX =>
    l1 Zd p (lf D F0) _ (TermLoc.sgnP D p) (sgnP_mem p) (fun i => by rw [tf, frame_cs]) (hpr1 p) hXS1 hw hwX
  have hA2 : ∀ p, ∀ w ∈ lattice₂ D Zd.M p Λ₂, w ∈ (locH Zd p).X (tLoc Zd p γ).f →
      w ∈ lattice₂ D Zd.M p (XLam Λ₂ (lf D F0)) := fun p w hw hwX =>
    l1 Zd p (lf D F0) _ (TermLoc.sgnP D p) (sgnP_mem p) (fun i => by rw [tf, frame_cs]) (hpr2 p) hXS2 hw hwX
  have hB1 : ∀ p, ∀ w ∈ lattice₂ D Zd.M p γ.lam, w ∈ (locH Zd p).X (tLoc Zd p γ).f' →
      w ∈ lattice₂ D Zd.M p (XLam γ.lam (repF γ)) := fun p w hw hwX =>
    l1 Zd p (repF γ) _ (sgnP' D p) (sgnP'_mem p) (fun i => by rw [BetaI.locF'_eq, frame_csG]; rfl) (hpr1' p) hXSx hw
      (Xle_tLoc Zd p γ hwX)
  have hB2 : ∀ p, ∀ w ∈ lattice₂ D Zd.M p Λ₂, w ∈ (locH Zd p).X (locF' Zd p F'₂) →
      w ∈ lattice₂ D Zd.M p (XLam Λ₂ (liftF F'₂)) := fun p w hw hwX =>
    l1 Zd p (liftF F'₂) _ (sgnP' D p) (sgnP'_mem p) (fun i => by rw [BetaI.locF'_eq, frame_csG]; rfl) (hpr2' p) hXS2'
      hw hwX
  intro x' hx' l hl l₂ hl₂ hll₂
  have hx'Λ := (Submodule.mem_inf.1 hx').1
  have hx'o : x' ∈ orth (VS D) (Xsp (repF γ)) := (Submodule.mem_inf.1 hx').2
  have hlΛ := (Submodule.mem_inf.1 hl).1
  have hlo : l ∈ orth (VS D) (Xsp (lf D F0)) := (Submodule.mem_inf.1 hl).2
  have hl₂Λ := (Submodule.mem_inf.1 hl₂).1
  have hl₂o : l₂ ∈ orth (VS D) (Xsp (lf D F0)) := (Submodule.mem_inf.1 hl₂).2
  have hβd : ∀ m ∈ orth (VS D) (Xsp (repF γ)), β₀ m - (v * β₀) m ∈ Xsp (liftF F'₂) := fun m hm => by
    have h := hvX _ (hβ₀o _ hm)
    have e : β₀ m - (v * β₀) m = -(v (β₀ m) - β₀ m) := by show _ - v _ = _; abel
    rw [e]; exact neg_mem h
  have hXo₂ : Xsp (liftF F'₂) ≤ orth (VS D) (Xsp (liftF F'₂)) :=
    BwdNA.X_le_orth (VS D) (Xsp (liftF F'₂)) (fun x hx y hy => NMoveP.hT_X_X F'₂.fl hx hy)
  have hRp : ∀ p (g : Loc.SplitG (Zd.M p).L), (Zd.M p).split = some g →
      Prod.map (φ' p) (LinearEquiv.refl (D.s.atP p).Ep ((locH Zd p).Wb (tLoc Zd p γ).f)) ''
        (locH Zd p).iotaGraph g (tLoc Zd p γ) = (locH Zd p).iotaGraph g (IotaBP.t2 Zd p γ F'₂ Λ₂) := fun p g hsp => by
    have := (hloc₂ p).2.2.2.2.2 g hsp
    rw [hφ p] at this
    exact this
  constructor
  · intro hmem
    obtain ⟨μ, hμ, ξ, hξ, ξ', hξ', heq⟩ := NgX_dec hmem
    refine mem_of_bcP Zd (IotaBP.isLattice_NgX hΛ₂lat _ _) fun p => ?_
    rcases hsp : (Zd.M p).split with _ | g
    · exact untyped_mem Zd p hsp _ _ (BwdNP.baseChange_mem_localLattice Zd (sub_mem hl₂Λ (hβΛ _ hx'Λ)) p)
    · exact IotaBP.fwd_typed Zd p g hsp γ F'₂ Λ₂ (φ' p) (hRp p g hsp) β₀ (v * β₀)
        (hP γ Z F'₂ φ φ' Λ₂ hB0 β₀ hiso hfr hW hO p) hβ₀o hβo hβd hβX hβΛ (hu p) hXo hXo' (hA2 p) (hB2 p)
        hx'Λ hx'o hlΛ hlo hl₂Λ hl₂o hll₂ hμ hξ hξ' heq
  · intro hmem
    obtain ⟨μ, hμ, ξ, hξ, ξ', hξ', heq⟩ := NgX_dec hmem
    refine mem_of_bcP Zd (IotaBP.isLattice_NgX hΛlat _ _) fun p => ?_
    rcases hsp : (Zd.M p).split with _ | g
    · exact untyped_mem Zd p hsp _ _ (BwdNP.baseChange_mem_localLattice Zd (sub_mem hlΛ hx'Λ) p)
    · exact IotaBP.bwd_typed Zd p g hsp γ F'₂ Λ₂ (φ' p) (hRp p g hsp) β₀ (v * β₀)
        (hP γ Z F'₂ φ φ' Λ₂ hB0 β₀ hiso hfr hW hO p) hβ₀o hβo hβd hβΛ (hu p) hXo hXo₂ (hA1 p) (hB1 p)
        hx'Λ hx'o hlΛ hlo hl₂Λ hl₂o hll₂ hμ hξ hξ' heq

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
