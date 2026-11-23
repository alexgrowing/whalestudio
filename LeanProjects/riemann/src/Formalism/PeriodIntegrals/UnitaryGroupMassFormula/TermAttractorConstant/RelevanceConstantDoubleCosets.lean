import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermAttractorConstant.LeadMinorEMulUpper
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermAttractorConstant.SpanFrameLtSucc

noncomputable section

open scoped Classical

namespace PI.TermAttrConst.UnitaryGroupMassFormula

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def RelevanceConstantDoubleCosets : Prop :=
  ∀ (D : D7) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (Λ : Submodule (𝓞 D.host.E) (VS D).V), IsRowLat D F0 Λ →
      RelFun Λ (lf D F0) (PD D Λ (lf D F0) u') D.host.F

def GenericityConstantDoubleCosets : Prop :=
  ∀ (D : D7) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (Λ : Submodule (𝓞 D.host.E) (VS D).V), IsRowLat D F0 Λ →
      GenFun Λ (lf D F0) (PD D Λ (lf D F0) u') (gS D)

theorem termGFun_holds (D : D7) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (_ : IsRowLat D F0 Λ) :
    GFun Λ (lf D F0) (PD D Λ (lf D F0) u') := gFun_all _ _ _

theorem termFun_of (hG : GenericityConstantDoubleCosets) (D : D7) (u u' : D.what₂.Word) : TermFun D u u' := by
  intro F0 Λ hΛ
  exact ⟨gFun_all _ _ _, cellFun_all _ _ _, relFun_all _ _ _ _, hG D u u' F0 Λ hΛ, feqFFun_all _ _ _⟩

end PI.TermAttrConst.UnitaryGroupMassFormula
