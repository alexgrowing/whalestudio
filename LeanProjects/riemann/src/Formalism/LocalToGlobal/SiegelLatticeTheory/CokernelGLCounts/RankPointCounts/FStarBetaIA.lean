import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdBetaK
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdN

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BetaI

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open BwdNP

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D)

section Frame

variable (p : PlF D) {T' : D.host.E} (G : LFlag (VS D) D.R.rS T')

theorem locF'_eq (b : Fin (D.R.rS + 1)) : locF' Zd p G b = sF' Zd p b • baseChange₂ D p (frame G b) := rfl

theorem bcP_frameG (b : Fin (D.R.rS + 1)) :
    baseChange₂ D p (frame G b) = (((isUnit_sF' Zd p b).unit⁻¹ : ((D.s.atP p).Ep)ˣ) : (D.s.atP p).Ep) • locF' Zd p G b := by
  rw [locF'_eq, smul_smul, (isUnit_sF' Zd p b).val_inv_mul, one_smul]

theorem frame_csG (i : Fin D.R.rS) : frame G i.castSucc = G.fl.e i := by
  simp [frame, FlagG.fvec]

theorem frame_lastG : frame G (Fin.last D.R.rS) = G.fl.z := by
  simp [frame, FlagG.fvec]

theorem sF'_last : sF' Zd p (Fin.last D.R.rS) = 1 := by
  unfold sF'
  rw [frFac_last' Zd p, mul_one]
  unfold TermLoc.sgnP'
  split
  · exact sgnP_last p
  · simp

theorem locF'_last : locF' Zd p G (Fin.last D.R.rS) = baseChange₂ D p G.fl.z := by
  rw [locF'_eq, sF'_last, one_smul, frame_lastG]

theorem bcP_X' {x : (VS D).V} (hx : x ∈ Xsp G) : baseChange₂ D p x ∈ (locH Zd p).X (locF' Zd p G) := by
  change x ∈ Submodule.span D.host.E (Set.range G.fl.e) at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [← frame_csG, bcP_frameG Zd p G]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c x _ hx => rw [Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂]; exact Submodule.smul_mem _ _ hx

theorem baseChangeAt_perp' {m : (VS D).V} (hm : m ∈ orth (VS D) (Xsp G)) :
    baseChange₂ D p m ∈ (locH Zd p).perp ((locH Zd p).X (locF' Zd p G)) := by
  show ∀ w ∈ (locH Zd p).X (locF' Zd p G), (locH Zd p).h (baseChange₂ D p m) w = 0
  intro w hw
  rw [h_eq]
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨i, rfl⟩ := hw
    simp only
    rw [locF'_eq, frame_csG, LocFacts.localForm_smul_right, ← h_eq, localForm_baseChange,
      (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hm _ (Submodule.subset_span ⟨i, rfl⟩), map_zero, mul_zero]
  | zero => exact LocFacts.localForm_zero_right Zd p _
  | add a b _ _ ha hb => rw [LocFacts.localForm_add_right, ha, hb, add_zero]
  | smul c w _ hw => rw [LocFacts.localForm_smul_right, hw, mul_zero]

end Frame

theorem z_memG {T' : D.host.E} (G : LFlag (VS D) D.R.rS T') {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hΛ : Submodule.IsLattice D.host.E Λ) (h : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λ) (locF' Zd p G)) :
    G.fl.z ∈ Λ :=
  mem_of_bcP Zd hΛ fun p => by rw [← locF'_last Zd p G]; exact (h p).1 _

theorem coef_intG {T' : D.host.E} (G : LFlag (VS D) D.R.rS T') {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hprim : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λ) (locF' Zd p G)) (c : Fin (D.R.rS + 1) → D.host.E)
    (hc : ∑ a, c a • frame G a ∈ Λ) : IsIntegral ℤ (c (Fin.last D.R.rS)) := by
  refine int_of_loc Zd fun p => ?_
  set m := ∑ a, c a • frame G a with hm
  have hbm : baseChange₂ D p m = ∑ a, ((D.s.atP p).ιE (c a) *
      ((((isUnit_sF' Zd p a).unit⁻¹ : ((D.s.atP p).Ep)ˣ)) : (D.s.atP p).Ep)) • locF' Zd p G a := by
    rw [hm, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂, bcP_frameG Zd p G, smul_smul]
  have hspan : baseChange₂ D p m ∈ Submodule.span (D.s.atP p).Ep (Set.range (locF' Zd p G)) := by
    rw [hbm]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have h2 := (hprim p).2.2 _ (baseChange_mem_localLattice Zd hc p) hspan
  obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h2
  have hli := (hprim p).2.1
  have hz : ∑ a, (((o a : (Zd.M p).L.O) : (D.s.atP p).Ep) -
      (D.s.atP p).ιE (c a) * ((((isUnit_sF' Zd p a).unit⁻¹ : ((D.s.atP p).Ep)ˣ)) : (D.s.atP p).Ep)) •
        locF' Zd p G a = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [← hbm, ← ho]
    simp only [sub_eq_zero]
    rfl
  have h3 := Fintype.linearIndependent_iff.1 hli _ hz (Fin.last D.R.rS)
  have key : ∀ {a : (D.s.atP p).Ep} (h : IsUnit a), a = 1 →
      (((h.unit⁻¹ : ((D.s.atP p).Ep)ˣ)) : (D.s.atP p).Ep) = 1 := by
    intro a h ha
    subst ha
    have : h.unit = 1 := Units.ext (IsUnit.unit_spec h)
    rw [this, inv_one, Units.val_one]
  have hone := key (isUnit_sF' Zd p (Fin.last D.R.rS)) (sF'_last Zd p)
  rw [hone, mul_one, sub_eq_zero] at h3
  rw [← h3]
  exact (o (Fin.last D.R.rS)).2

theorem exists_yG {T' : D.host.E} (G : LFlag (VS D) D.R.rS T') {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hΛ : Submodule.IsLattice D.host.E Λ) (hSD : BwdNA.SD (VS D) Λ)
    (hprim : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λ) (locF' Zd p G)) (hzX : G.fl.z ∉ Xsp G) :
    ∃ y ∈ Λ, y ∈ orth (VS D) (Xsp G) ∧ (VS D).hT y G.fl.z = 1 := by
  obtain ⟨f, hfz, hfX⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hzX inferInstance
  let ρ : Module.Dual D.host.E (VS D).V := (f G.fl.z)⁻¹ • f
  have hρz : ρ G.fl.z = 1 := by
    simp only [ρ, LinearMap.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ hfz
  have hρX : ∀ x ∈ Xsp G, ρ x = 0 := fun x hx => by
    have h1 : f x ∈ (Xsp G).map f := ⟨x, hx, rfl⟩
    rw [hfX, Submodule.mem_bot] at h1
    simp only [ρ, LinearMap.smul_apply, smul_eq_mul, h1, mul_zero]
  have hρe : ∀ i : Fin D.R.rS, ρ (frame G i.castSucc) = 0 := fun i => by
    rw [frame_csG]; exact hρX _ (Submodule.subset_span ⟨i, rfl⟩)
  have hρl : ρ (frame G (Fin.last D.R.rS)) = 1 := by
    rw [frame_lastG, hρz]
  obtain ⟨v, hv⟩ := BwdNA.riesz (VS D) ρ
  let U : Submodule D.host.E (VS D).V := Submodule.span D.host.E (Set.range (frame G))
  have hint : ∀ m ∈ Λ, m ∈ U → IsIntegral ℤ ((VS D).hT m v) := fun m hm hmU => by
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hmU
    have hρm : ρ m = c (Fin.last D.R.rS) := by
      rw [← hc, map_sum, Fin.sum_univ_castSucc]
      simp only [map_smul, smul_eq_mul, hρe, mul_zero, Finset.sum_const_zero, zero_add, hρl, mul_one]
    rw [BwdNA.hsw (VS D) v m, hv, hρm]
    exact BwdNA.isInt_star (coef_intG Zd G hprim c (by rw [hc]; exact hm))
  obtain ⟨w, hwΛ, hvw⟩ := BwdNA.dual_sum (VS D) Λ hΛ hSD U v hint
  have hw : ∀ a, (VS D).hT w (frame G a) = ρ (frame G a) := fun a => by
    have h0 := (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hvw _ (Submodule.subset_span ⟨a, rfl⟩)
    rw [map_sub, sub_eq_zero] at h0
    rw [BwdNA.hsw (VS D) (frame G a) w, ← h0, ← BwdNA.hsw (VS D) (frame G a) v, hv]
  refine ⟨w, hwΛ, (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).2 fun x hx => ?_, ?_⟩
  · change x ∈ Submodule.span D.host.E (Set.range G.fl.e) at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [BwdNA.hsw (VS D) w (G.fl.e i), ← frame_csG, hw, hρe, star_zero]
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply, ha, hb, add_zero]
    | smul c x _ hx => rw [BwdNA.hT_smulL, hx, mul_zero]
  · rw [← frame_lastG, hw, hρl]

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BetaI
