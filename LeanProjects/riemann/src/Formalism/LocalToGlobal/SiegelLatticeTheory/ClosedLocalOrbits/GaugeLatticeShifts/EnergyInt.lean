import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StepIntOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj
open scoped ENNReal

namespace Formalism.L2.SG.RealObj.EnergyInt

def LocOrbG : Prop :=
  ∀ (D : D7), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (X : HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ), 0 < sc →
    ∀ c ∈ Good X u u', ∀ γ, HasDiag X u u' sc c γ → ∀ v : InfinitePlace X.B.I.F,
      ∫⁻ x, ‖X.Wloc u v x‖ₑ * ‖X.Wloc u' v ((γ v)⁻¹ * x)‖ₑ ∂(Formalism.REAL.muG (X.B.I.ε v)) < ⊤

def StepIntG : Prop :=
  ∀ (D : D7), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (X : HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ), 0 < sc →
    ∀ c ∈ Good X u u', ∀ γ, HasDiag X u u' sc c γ →
      TermOp.OOInt (Formalism.L2.SG.ProjRows.muInf X.B.I) Set.univ (X.Wu u) (X.Wu u') γ

theorem lint_prod {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (γ : X.B.I.Ginf) :
    ∫⁻ x, ‖X.Wu u x‖ₑ * ‖X.Wu u' (γ⁻¹ * x)‖ₑ ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) =
      ∏ v, ∫⁻ x, ‖X.Wloc u v x‖ₑ * ‖X.Wloc u' v ((γ v)⁻¹ * x)‖ₑ ∂(Formalism.REAL.muG (X.B.I.ε v)) := by
  have hm : ∀ v, Measurable (fun x : Formalism.REAL.UJ (X.B.I.ε v) =>
      ‖X.Wloc u v x‖ₑ * ‖X.Wloc u' v ((γ v)⁻¹ * x)‖ₑ) := by
    intro v
    exact ((X.Wloc_cont u v).enorm.measurable).mul
      (((X.Wloc_cont u' v).comp (continuous_const.mul continuous_id)).enorm.measurable)
  rw [← Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.lintegral_pi_prod (fun v => Formalism.REAL.muG (X.B.I.ε v)) _ hm]
  simp_rw [Formalism.L2.SG.Pf.WuDec.enorm_Wu, ← Finset.prod_mul_distrib]
  rfl

theorem stepIntG_of_loc (h : LocOrbG) : StepIntG := by
  intro D hG X u u' sc hsc c hc γ hγ
  apply Formalism.L2.SG.RealObj.StepIntOf.Steps.stIntOfLint D X u u' γ
  rw [lint_prod]
  exact ENNReal.prod_lt_top fun v _ => h D hG X u u' sc hsc c hc γ hγ v

end Formalism.L2.SG.RealObj.EnergyInt
