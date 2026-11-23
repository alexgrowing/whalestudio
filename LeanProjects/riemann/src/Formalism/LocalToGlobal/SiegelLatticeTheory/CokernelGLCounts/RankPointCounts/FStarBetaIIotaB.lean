import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaIIotaA

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.IotaBP

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (p : PlF D)

theorem xi_mem {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T : D.host.E} {F : LFlag (VS D) D.R.rS T} {x : (VS D).V}
    (hx : x ∈ XLam Λ F) : x ∈ Λ := (Submodule.mem_inf.1 hx).1

theorem g1 {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T)
    (F' : LFlag (VS D) D.R.rS T') (t : Loc.Term (Vp D p) (Zd.M p) D.R.rS) (hLam : t.abelian₂ = lattice₂ D Zd.M p Λ)
    (g : Loc.SplitG (Zd.M p).L) (hs : (Zd.M p).split = some g) {y y' l ξ ξ' : (VS D).V} (hy : y ∈ Λ) (hy' : y' ∈ Λ)
    (hl : l ∈ Λ) (hξ : ξ ∈ XLam Λ F) (hξ' : ξ' ∈ XLam Λ F')
    (heq : y - y' = ((gS D : ℕ) : D.host.E) • l + ξ + ξ')
    (hp1 : baseChange₂ D p (y - ξ) ∈ (locH Zd p).perp ((locH Zd p).X t.f))
    (hp2 : baseChange₂ D p (y' + ξ') ∈ (locH Zd p).perp ((locH Zd p).X t.f')) :
    ((locH Zd p).mkW t.f' ⟨baseChange₂ D p (y' + ξ'), hp2⟩, (locH Zd p).mkW t.f ⟨baseChange₂ D p (y - ξ), hp1⟩) ∈
      (locH Zd p).iotaGraph g t := by
  obtain ⟨w, hw, w', -, he, -⟩ := gS_typed Zd p g hs
  refine ⟨⟨_, hp2⟩, ⟨_, hp1⟩, ?_, ?_, ?_, rfl⟩
  · rw [hLam]; exact BwdNP.baseChange_mem_localLattice Zd (add_mem hy' (xi_mem hξ')) p
  · rw [hLam]; exact BwdNP.baseChange_mem_localLattice Zd (sub_mem hy (xi_mem hξ)) p
  · have hv : y - ξ - (y' + ξ') = ((gS D : ℕ) : D.host.E) • l := by
      rw [show y - ξ - (y' + ξ') = (y - y') - ξ - ξ' by abel, heq]; abel
    have e : baseChange₂ D p (y - ξ) - baseChange₂ D p (y' + ξ') =
        algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) • (w • baseChange₂ D p l) := by
      rw [← map_sub, hv, Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂, he, mul_smul]
    show baseChange₂ D p (y - ξ) - baseChange₂ D p (y' + ξ') ∈ _
    rw [e, hLam]
    exact Submodule.subset_span ⟨w • baseChange₂ D p l, Formalism.L2.SG.Pf.LocalDenominators.smul_mem_localLattice Zd p hw (BwdNP.baseChange_mem_localLattice Zd hl p), rfl⟩

theorem g2 {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T)
    (F' : LFlag (VS D) D.R.rS T') (t : Loc.Term (Vp D p) (Zd.M p) D.R.rS) (hLam : t.abelian₂ = lattice₂ D Zd.M p Λ)
    (g : Loc.SplitG (Zd.M p).L) (hs : (Zd.M p).split = some g) {y y' : (VS D).V} (hy : y ∈ Λ) (hy' : y' ∈ Λ)
    (hp1 : baseChange₂ D p y ∈ (locH Zd p).perp ((locH Zd p).X t.f))
    (hp2 : baseChange₂ D p y' ∈ (locH Zd p).perp ((locH Zd p).X t.f'))
    (hmem : ((locH Zd p).mkW t.f' ⟨baseChange₂ D p y', hp2⟩, (locH Zd p).mkW t.f ⟨baseChange₂ D p y, hp1⟩) ∈
      (locH Zd p).iotaGraph g t)
    (hA : ∀ v ∈ lattice₂ D Zd.M p Λ, v ∈ (locH Zd p).X t.f → v ∈ lattice₂ D Zd.M p (XLam Λ F))
    (hB : ∀ v ∈ lattice₂ D Zd.M p Λ, v ∈ (locH Zd p).X t.f' → v ∈ lattice₂ D Zd.M p (XLam Λ F')) :
    baseChange₂ D p (y - y') ∈ lattice₂ D Zd.M p (NgX Λ (gS D) F F') := by
  obtain ⟨x'', x, hx''Λ, hxΛ, hdiff, heq⟩ := hmem
  obtain ⟨h1, h2⟩ := Prod.mk.inj heq
  rw [hLam] at hx''Λ hxΛ hdiff
  have d1 : baseChange₂ D p y' - (x'' : Vp D p) ∈ (locH Zd p).X t.f' := by
    have := (Submodule.Quotient.eq _).1 h1
    simpa using this
  have d2 : baseChange₂ D p y - (x : Vp D p) ∈ (locH Zd p).X t.f := by
    have := (Submodule.Quotient.eq _).1 h2
    simpa using this
  have hXA : XLam Λ F ≤ NgX Λ (gS D) F F' := le_sup_right.trans le_sup_left
  have hXB : XLam Λ F' ≤ NgX Λ (gS D) F F' := le_sup_right
  have a1 := localLattice_mono Zd p hXA (hA _ (sub_mem (BwdNP.baseChange_mem_localLattice Zd hy p) hxΛ) d2)
  have a2 := localLattice_mono Zd p hXB (hB _ (sub_mem (BwdNP.baseChange_mem_localLattice Zd hy' p) hx''Λ) d1)
  have a3 : (x : Vp D p) - x'' ∈ lattice₂ D Zd.M p (NgX Λ (gS D) F F') := by
    refine (Submodule.span_le.2 ?_) hdiff
    rintro _ ⟨v, hv, rfl⟩
    exact typed_q_mem Zd p g hs F F' hv
  have e : baseChange₂ D p (y - y') = (baseChange₂ D p y - x) + ((x : Vp D p) - x'') - (baseChange₂ D p y' - x'') := by
    rw [map_sub]; abel
  rw [e]
  exact sub_mem (add_mem a1 a3) a2

theorem Xle_tLoc {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (γ : TermDef.Term D u u' F0 what₂) :
    (locH Zd p).X (tLoc Zd p γ).f' ≤ (locH Zd p).X (locF' Zd p (repF γ)) := by
  obtain ⟨hξ1, hξ2⟩ := inv_unitri _ (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).1 (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).2
  obtain ⟨hC0, -, -⟩ := Cm_props Zd p (admXi D γ.lam (lf D F0) (repF γ))⁻¹ hξ1 hξ2
  have hf : ∀ b, (tLoc Zd p γ).f' b = GeneratorChange.comb (Cm Zd p (admXi D γ.lam (lf D F0) (repF γ))⁻¹) (locF' Zd p (repF γ)) b :=
    fun b => (comb_Cm Zd p (repF γ) _ b).symm
  rw [Loc.HermSp.X, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  simp only
  rw [hf, GeneratorChange.comb, Fin.sum_univ_castSucc]
  refine add_mem (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)) ?_
  rw [hC0 _ _ (Fin.castSucc_lt_last i), zero_smul]
  exact zero_mem _

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.IotaBP
