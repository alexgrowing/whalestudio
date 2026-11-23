import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaIC
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AdmissibleLocalPartner
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfQ

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.IotaBP

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (p : PlF D)

theorem gS_typed (g : Loc.SplitG (Zd.M p).L) (hs : (Zd.M p).split = some g) :
    ∃ w ∈ (D.s.atP p).O, ∃ w' ∈ (D.s.atP p).O,
      (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) * w ∧
        w * w' = 1 := by
  obtain ⟨sg, hsg, hq, -⟩ := typed_data Zd p g hs
  refine ⟨(D.s.atP p).ιE ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : D.host.E), ?_, (D.s.atP p).ιE (uP p : D.host.E),
    Formalism.L2.SG.Pf.LocFacts.unitPart_mem₂ p, ?_, ?_⟩
  · rw [map_natCast]; exact natCast_mem _ _
  · rw [hq, sg.q_eq, ← Formalism.MainNotions.BridgeLemma.gpart_mul_oth p, Formalism.MainNotions.BridgeLemma.gpart_some p sg hsg]
    simp only [Nat.cast_mul, map_mul, map_natCast]
  · rw [← map_mul, Formalism.MainNotions.BridgeLemma.unitAt_eq p]
    have h0 : ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : D.host.E) ≠ 0 := by
      exact_mod_cast Formalism.MainNotions.BridgeLemma.oth_ne_zero p
    push_cast
    rw [mul_inv_cancel₀ h0, map_one]

theorem localLattice_mono {A B : Submodule (𝓞 D.host.E) (VS D).V} (h : A ≤ B) : lattice₂ D Zd.M p A ≤ lattice₂ D Zd.M p B :=
  Submodule.span_mono (Set.image_mono h)

theorem mem_O_M {a : (D.s.atP p).Ep} (ha : a ∈ (D.s.atP p).O) : a ∈ (Zd.M p).L.O := by
  rw [Formalism.L2.SG.Pf.LocalDenominators.hO Zd p]; exact ha

theorem smul_gS_mem {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T)
    (F' : LFlag (VS D) D.R.rS T') {v : Vp D p} (hv : v ∈ lattice₂ D Zd.M p Λ) :
    (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • v ∈ lattice₂ D Zd.M p (NgX Λ (gS D) F F') := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨y, hy, rfl⟩ := hv
    rw [← Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂]
    refine Submodule.subset_span ⟨_, ?_, rfl⟩
    have h1 : ((gS D : ℕ) : D.host.E) • y = ((gS D : ℕ) : 𝓞 D.host.E) • y := by
      rw [← algebraMap_smul D.host.E ((gS D : ℕ) : 𝓞 D.host.E) y, map_natCast]
    rw [SetLike.mem_coe, h1]
    refine Submodule.mem_sup_left (Submodule.mem_sup_left ?_)
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hy
  | zero => rw [smul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul o v _ hv =>
    have e : (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • (o • v) = o • ((D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • v) := by
      show _ • ((o : (D.s.atP p).Ep) • v) = (o : (D.s.atP p).Ep) • _
      rw [smul_smul, smul_smul, mul_comm]
    rw [e]; exact Submodule.smul_mem _ _ hv

theorem untyped_mem (hs : (Zd.M p).split = none) {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T T' : D.host.E}
    (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') {v : Vp D p} (hv : v ∈ lattice₂ D Zd.M p Λ) :
    v ∈ lattice₂ D Zd.M p (NgX Λ (gS D) F F') := by
  have e := Formalism.L2.SG.Pf.StabIntSh.gS_mul_uP Zd.δ Zd.M Zd.agree p hs
  have hv' : v = (D.s.atP p).ιE (uP p : D.host.E) • ((D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • v) := by
    rw [smul_smul, mul_comm, e, one_smul]
  rw [hv']
  exact Formalism.L2.SG.Pf.LocalDenominators.smul_mem_localLattice Zd p (Formalism.L2.SG.Pf.LocFacts.unitPart_mem₂ p) (smul_gS_mem Zd p F F' hv)

theorem typed_q_mem (g : Loc.SplitG (Zd.M p).L) (hs : (Zd.M p).split = some g) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') {v : Vp D p}
    (hv : v ∈ lattice₂ D Zd.M p Λ) :
    algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) • v ∈ lattice₂ D Zd.M p (NgX Λ (gS D) F F') := by
  obtain ⟨w, -, w', hw', he, hww⟩ := gS_typed Zd p g hs
  have e : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) • v =
      (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • (w' • v) := by
    rw [he, smul_smul, mul_assoc, hww, mul_one]
  rw [e]
  exact smul_gS_mem Zd p F F' (Formalism.L2.SG.Pf.LocalDenominators.smul_mem_localLattice Zd p hw' hv)

theorem l1 {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T' : D.host.E} (G : LFlag (VS D) D.R.rS T')
    (f : Fin (D.R.rS + 1) → Vp D p) (s : Fin (D.R.rS + 1) → (D.s.atP p).Ep) (hs : ∀ a, s a ∈ (D.s.atP p).O)
    (hf : ∀ i : Fin D.R.rS, f i.castSucc = (s i.castSucc * frFac Zd.δ p i.castSucc) • baseChange₂ D p (G.fl.e i))
    (hprim : (locH Zd p).Prim (lattice₂ D Zd.M p Λ) f) (hXS : XLam Λ G = XS D G.fl) {v : Vp D p}
    (hv : v ∈ lattice₂ D Zd.M p Λ) (hvX : v ∈ (locH Zd p).X f) : v ∈ lattice₂ D Zd.M p (XLam Λ G) := by
  have hvE : v ∈ Submodule.span (D.s.atP p).Ep (Set.range f) :=
    Submodule.span_mono (Set.range_comp_subset_range _ _) hvX
  have hvO := hprim.2.2 v hv hvE
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (Zd.M p).L.O).1 hvO
  obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun (D.s.atP p).Ep).1 hvX
  have key : (c (Fin.last D.R.rS) : (D.s.atP p).Ep) = 0 := by
    have h0 : ∑ a, ((c a : (D.s.atP p).Ep) - Fin.snoc (α := fun _ => (D.s.atP p).Ep) e 0 a) • f a = 0 := by
      simp_rw [sub_smul]
      rw [Finset.sum_sub_distrib, Fin.sum_univ_castSucc (f := fun a => Fin.snoc (α := fun _ => (D.s.atP p).Ep) e 0 a • f a)]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, zero_smul, add_zero]
      rw [he, ← hc, sub_eq_zero]
      rfl
    have := Fintype.linearIndependent_iff.1 hprim.2.1 _ h0 (Fin.last D.R.rS)
    simpa using this
  rw [← hc, Fin.sum_univ_castSucc]
  refine add_mem (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_) ?_
  · rw [hf, hXS, Formalism.L2.SG.Pf.BBTie.bt_latP_XS Zd p (Formalism.L2.SG.Pf.locDiffC_holds D Zd) G.fl, mul_smul]
    have hm : frFac Zd.δ p i.castSucc • baseChange₂ D p (G.fl.e i) ∈ Submodule.span (Zd.M p).L.O
        (Set.range fun a : Fin D.R.rS => frFac Zd.δ p a.castSucc • baseChange₂ D p (G.fl.e a)) := Submodule.subset_span ⟨i, rfl⟩
    exact Submodule.smul_mem _ (⟨s i.castSucc, mem_O_M Zd p (hs _)⟩ : (Zd.M p).L.O) hm
  · have : c (Fin.last D.R.rS) • f (Fin.last D.R.rS) = 0 := by
      rw [Subring.smul_def, key, zero_smul]
    rw [this]; exact zero_mem _

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.IotaBP
