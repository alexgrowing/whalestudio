import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DecompPhaseCOf

noncomputable section

open scoped Classical ComplexConjugate

namespace Formalism.L2.SG.Pf.RowForm

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.MassDataForm MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
  (κ : Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)

def RealDecompC : Prop :=
  ∀ t : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'), t.relevant → t.G ≠ 0 →
    (∃ γ, Formalism.L2.SG.RealObj.IsPtRep X u u' (Formalism.L2.SG.PairVal.ptOf t.toTerm) γ) ∧
      ∀ γ, Formalism.L2.SG.RealObj.IsPtRep X u u' (Formalism.L2.SG.PairVal.ptOf t.toTerm) γ →
        ∃ g ∈ X.SinfU u, ∃ g' ∈ X.SinfU u', t.pt.1 = g * γ * g'⁻¹

theorem isPtRep_gamW {w : Point D.host.E (D.R.rS + 1)} (h : ∃ γ, Formalism.L2.SG.RealObj.IsPtRep X u u' w γ) :
    Formalism.L2.SG.RealObj.IsPtRep X u u' w (Formalism.L2.SG.RealObj.gamW X u u' w) := by
  unfold Formalism.L2.SG.RealObj.gamW
  rw [dif_pos h]
  exact h.choose_spec

theorem realDecompC_gamW (h : RealDecompC X Y u u')
    (t : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) (hrel : t.relevant) (hG : t.G ≠ 0) :
    (∃ γ, Formalism.L2.SG.RealObj.IsPtRep X u u' (Formalism.L2.SG.PairVal.ptOf t.toTerm) γ) ∧
      ∃ g ∈ X.SinfU u, ∃ g' ∈ X.SinfU u',
        t.pt.1 = g * Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf t.toTerm) * g'⁻¹ := by
  obtain ⟨hex, hall⟩ := h t hrel hG
  exact ⟨hex, hall _ (isPtRep_gamW X u u' hex)⟩

theorem realDecomp_G_ne (s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'))
    (h : (Y.tO u u').G s ≠ 0) : s.G ≠ 0 := by
  intro h0
  apply h
  show Formalism.L2.SG.TermOp.Gt s = 0
  simp [Formalism.L2.SG.TermOp.Gt, h0]

theorem liftDecompC_of_real (h : RealDecompC X Y u u') : LiftDecompC X Y u u' κ := by
  intro R ρ s hrel
  exact realDecompC_gamW X Y u u' h s.1 hrel (realDecomp_G_ne X Y u u' s.1 s.2.1)

theorem decompPhaseC_of_real (h : RealDecompC X Y u u') (h6 : PhaseTieC X Y u u' κ) : DecompPhaseC X Y u u' κ := by
  intro R ρ s hrel
  obtain ⟨hex, g, hg, g', hg', heq⟩ := liftDecompC_of_real X Y u u' κ h R ρ s hrel
  exact ⟨hex, g, hg, g', hg', heq, h6 R ρ s hrel g hg g' hg' heq⟩

end Formalism.L2.SG.Pf.RowForm
