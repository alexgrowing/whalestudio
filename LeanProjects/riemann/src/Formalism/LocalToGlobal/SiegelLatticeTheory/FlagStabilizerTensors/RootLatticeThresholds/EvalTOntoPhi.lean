import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTOntoEqv
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTOnto
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DstarIdxPf

noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.L2.Theta Formalism.L2.SG.RowDict
open scoped InnerProductSpace

namespace Formalism.L2.SG.EvalTOntoPhi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem regAlg : (∀ a b, X.B.R (a * b) = (X.B.R a).comp (X.B.R b)) ∧ X.B.R 1 = 1 ∧ ∀ a F, ‖X.B.R a F‖ = ‖F‖ := by
  have := X.B.sf
  have := X.B.haar
  exact Formalism.L2.SG.Pf.reg_alg Formalism.L2.SG.Closed.UnimodGf_holds X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R X.B.R_spec

theorem inner_reg (a : X.B.I.GA) (x z : L2X X) : ⟪x, X.B.R a z⟫_ℂ = ⟪X.B.R a⁻¹ x, z⟫_ℂ := by
  obtain ⟨hmul, hone, hiso⟩ := regAlg X
  have := Formalism.L2.SG.Pf.inner_orbit X.B.R hmul hiso a⁻¹ 1 x z
  rw [hone, ContinuousLinearMap.one_apply, inv_inv, mul_one] at this
  exact this.symm

variable {X}

end Formalism.L2.SG.EvalTOntoPhi

end
