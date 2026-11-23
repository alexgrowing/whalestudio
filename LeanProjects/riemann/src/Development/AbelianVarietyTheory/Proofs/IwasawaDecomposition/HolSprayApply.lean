import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousAndSmul

set_option autoImplicit false

noncomputable section

open ReciprocityTheory.L2DbarEstimates

namespace GlobalTheory.ChernReg

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

def holSpray (b : V d → Matrix (Fin d) (Fin d) ℂ) (f : V d × V d → E) (q : V d × V d) : E :=
  GlobalTheory.del f q (q.2, -christoffel b q.1 q.2)

theorem holSpray_apply (b : V d → Matrix (Fin d) (Fin d) ℂ) (f : V d × V d → E) (q : V d × V d) :
    holSpray b f q = GlobalTheory.del f q (q.2, -christoffel b q.1 q.2) := rfl

end GlobalTheory.ChernReg
