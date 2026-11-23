import Formalism.LocalToGlobal.ProjectiveLattices.RecPJThAllNeBot

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open Formalism.MainNotions

variable {D : Formalism.BasicNotions.D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

def EtVal (X : WeightAlgebra.PJ D B P j) (i : ℕ)
    (η : B.Cusp j (WeightAlgebra.wscalar D j (WeightAlgebra.g0 D * i) (by unfold WeightAlgebra.g0; exact ⟨5 ^ 4 * D.R.r * i, by ring⟩))) : Prop :=
  ∀ la (y : X.Pt la), ((2 * i * X.phiC la y : ℝ) : EReal) ≤ X.vAt la y (X.inc _ η)

end Formalism.MainNotions.ModuliIntegralCharts.H1
