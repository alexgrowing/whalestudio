import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartialIsometryExtension
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsotropicSpanOrthogonalAnisotropicVector

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.OrthogonalLocalComplement

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open BwdCut BwdBetaCut BwdNP BetaI

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem frameAct_mem_Xplus {T' : D.host.E} (G : LFlag (VS D) D.R.rS T')
    (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E)) (b : Fin (D.R.rS + 1)) :
    frameAct (frame G) ξ b ∈ G.fl.Xplus := by
  rw [SpanOmPf.Xplus_eq]
  show ∑ a, ((ξ a b : 𝓞 D.host.E) : D.host.E) • frame G a ∈ _
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem form_zero (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) {w : (VS D).V}
    (hw : w ∈ orth (VS D) (F0.Xplus ⊔ (repF γ).fl.Xplus)) {v : (VS D).V}
    (hv : v ∈ F0.Xplus ⊔ (repF γ).fl.Xplus) (c : (D.s.atP p).Ep) :
    LocFacts₂ Zd.M p (baseChange₂ D p w) (c • baseChange₂ D p v) = 0 := by
  rw [LocFacts.localForm_smul_right, ← h_eq, localForm_baseChange, (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hw v hv, map_zero,
    mul_zero]

theorem baseChange_mem_W0 (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) {w : (VS D).V}
    (hw : w ∈ orth (VS D) (F0.Xplus ⊔ (repF γ).fl.Xplus)) :
    baseChange₂ D p w ∈ (locH Zd p).W0 (tLoc Zd p γ).f (tLoc Zd p γ).f' := by
  show ∀ x ∈ (locH Zd p).Xp (tLoc Zd p γ).f ⊔ (locH Zd p).Xp (tLoc Zd p γ).f', (locH Zd p).h (baseChange₂ D p w) x = 0
  intro x hx
  rw [h_eq]
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
  clear hx
  rw [LocFacts.localForm_add_right]
  have hA : LocFacts₂ Zd.M p (baseChange₂ D p w) a = 0 := by
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [tf]
      refine form_zero Zd p γ hw (Submodule.mem_sup_left ?_) _
      rw [SpanOmPf.Xplus_eq]
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => exact LocFacts.localForm_zero_right Zd p _
    | add a b _ _ ha hb => rw [LocFacts.localForm_add_right, ha, hb, add_zero]
    | smul c w _ hw => rw [LocFacts.localForm_smul_right, hw, mul_zero]
  clear ha
  have hB : LocFacts₂ Zd.M p (baseChange₂ D p w) b = 0 := by
    induction hb using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [tf']
      exact form_zero Zd p γ hw (Submodule.mem_sup_right (frameAct_mem_Xplus _ _ i)) _
    | zero => exact LocFacts.localForm_zero_right Zd p _
    | add a b _ _ ha hb => rw [LocFacts.localForm_add_right, ha, hb, add_zero]
    | smul c w _ hw => rw [LocFacts.localForm_smul_right, hw, mul_zero]
  rw [hA, hB, add_zero]

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.OrthogonalLocalComplement
