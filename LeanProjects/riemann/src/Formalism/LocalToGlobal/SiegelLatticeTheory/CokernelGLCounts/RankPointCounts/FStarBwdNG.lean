import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdNF

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNP

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

section Place

variable (p : PlF D) (γ : TermDef.Term D u u' F0 what₂)
  (hu : ∀ a, IsUnit (TermLoc.sgnP D p a * frFac Zd.δ p a))

include hu in
theorem baseChangeAt_frame_eq (a : Fin (D.R.rS + 1)) :
    baseChange₂ D p (frame (lf D F0) a) = ((hu a).unit⁻¹ : ((D.s.atP p).Ep)ˣ) • (tLoc Zd p γ).f a := by
  rw [tf, Units.smul_def, smul_smul, (hu a).val_inv_mul, one_smul]

include hu in
theorem bcP_X {x : (VS D).V} (hx : x ∈ Xsp (lf D F0)) : baseChange₂ D p x ∈ (locH Zd p).X (tLoc Zd p γ).f := by
  change x ∈ Submodule.span D.host.E (Set.range F0.e) at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [← frame_cs, baseChangeAt_frame_eq Zd p γ hu, Units.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c x _ hx => rw [Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂]; exact Submodule.smul_mem _ _ hx

theorem baseChange_mem_perp_sup {m : (VS D).V} (hm : m ∈ orth (VS D) (Xsp (lf D F0))) :
    baseChange₂ D p m ∈ (locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f) := by
  show ∀ w ∈ (locH Zd p).X (tLoc Zd p γ).f, (locH Zd p).h (baseChange₂ D p m) w = 0
  intro w hw
  rw [h_eq]
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨i, rfl⟩ := hw
    simp only
    rw [tf, frame_cs, LocFacts.localForm_smul_right, ← h_eq, localForm_baseChange,
      (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hm _ (Submodule.subset_span ⟨i, rfl⟩), map_zero, mul_zero]
  | zero => exact LocFacts.localForm_zero_right Zd p _
  | add a b _ _ ha hb => rw [LocFacts.localForm_add_right, ha, hb, add_zero]
  | smul c w _ hw => rw [LocFacts.localForm_smul_right, hw, mul_zero]

theorem h_X_perp {w v : Vp D p} (hw : w ∈ (locH Zd p).X (tLoc Zd p γ).f)
    (hv : v ∈ (locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f)) : (locH Zd p).h w v = 0 := by
  rw [(locH Zd p).h_herm v w, (show (locH Zd p).h v w = 0 from hv w hw), map_zero]

end Place

theorem pair_int (γ : TermDef.Term D u u' F0 what₂) {Λ₁ Λ₂ : Submodule (𝓞 D.host.E) (VS D).V}
    (hSD₁ : ∀ p, (locH Zd p).IsSelfDual (lattice₂ D Zd.M p Λ₁))
    (hL : ∀ p, (locH Zd p).Lset (lattice₂ D Zd.M p Λ₂) (tLoc Zd p γ).f ⊆
      (locH Zd p).Lset (lattice₂ D Zd.M p Λ₁) (tLoc Zd p γ).f)
    {x m : (VS D).V} (hx : x ∈ Λ₂) (hxo : x ∈ orth (VS D) (Xsp (lf D F0))) (hm : m ∈ Λ₁)
    (hmo : m ∈ orth (VS D) (Xsp (lf D F0))) : IsIntegral ℤ ((VS D).hT m x) := by
  refine int_of_loc Zd fun p => ?_
  rw [← localForm_baseChange]
  have hv := baseChange_mem_perp_sup Zd p γ hxo
  have hmem : (locH Zd p).mkW (tLoc Zd p γ).f ⟨baseChange₂ D p x, hv⟩ ∈
      (locH Zd p).Lset (lattice₂ D Zd.M p Λ₂) (tLoc Zd p γ).f := ⟨⟨baseChange₂ D p x, hv⟩, baseChange_mem_localLattice Zd hx p, rfl⟩
  obtain ⟨x'', hx''Λ, hx''eq⟩ := hL p hmem
  have hdiff : (baseChange₂ D p x) - (x'' : Vp D p) ∈ (locH Zd p).X (tLoc Zd p γ).f := by
    have := (Submodule.Quotient.eq _).1 hx''eq.symm
    simpa using this
  have e : baseChange₂ D p x = (x'' : Vp D p) + ((baseChange₂ D p x) - (x'' : Vp D p)) := by abel
  rw [e, (locH Zd p).h_add_left, h_X_perp Zd p γ hdiff (baseChange_mem_perp_sup Zd p γ hmo), add_zero]
  exact ((hSD₁ p).2.2 x'').1 hx''Λ (baseChange₂ D p m) (baseChange_mem_localLattice Zd hm p)

theorem memX (γ : TermDef.Term D u u' F0 what₂) {Λa Λb : Submodule (𝓞 D.host.E) (VS D).V}
    (ha : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λa) (tLoc Zd p γ).f)
    (hb : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λb) (tLoc Zd p γ).f) (hΛb : Submodule.IsLattice D.host.E Λb)
    (hu : ∀ p a, IsUnit (TermLoc.sgnP D p a * frFac Zd.δ p a)) {x : (VS D).V} (hx : x ∈ Xsp (lf D F0))
    (hxa : x ∈ Λa) : x ∈ Λb := by
  refine mem_of_bcP Zd hΛb fun p => ?_
  have h1 : baseChange₂ D p x ∈ Submodule.span (D.s.atP p).Ep (Set.range (tLoc Zd p γ).f) :=
    Submodule.span_mono (Set.range_comp_subset_range _ _) (bcP_X Zd p γ (hu p) hx)
  have h2 := (ha p).2.2 _ (baseChange_mem_localLattice Zd hxa p) h1
  exact Submodule.span_le.2 (Set.range_subset_iff.2 fun a => (hb p).1 a) h2

theorem z_mem (γ : TermDef.Term D u u' F0 what₂) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hΛ : Submodule.IsLattice D.host.E Λ) (h : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λ) (tLoc Zd p γ).f) :
    F0.z ∈ Λ :=
  mem_of_bcP Zd hΛ fun p => by rw [← tf_last Zd p γ]; exact (h p).1 _

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNP
