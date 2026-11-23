import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FirstDeriv
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.ThmSUniform
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.EDecomp
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.MPlaces

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.FG.SolveVAux (Low)
open Formalism.FG.IntegralSubstitution (integral_mul integral_pow integral_one integralSubstV)
open TwoS (Cg cg_refl cg_of_eq cg_symm cg_trans cg_add cg_sum cg_mul cg_pow
  integral_add integral_neg integral_sum integral_C integral_X integral_zero pinv_le_one
  constantCoeff_sSub integral_sSub)

namespace ExpansionsAtPlaces

section ModP

variable {K : Type} [NormedField K] [IsUltrametricDist K] {ν r0 r1 : ℕ}

end ModP

section Places

variable {K Pl : Type} [Field K] {ι κ : Pl → Type}

end Places

theorem integral_prod {K ι α : Type} [NormedField K] [IsUltrametricDist K] (s : Finset α)
    (x : α → MvPowerSeries ι K) (hx : ∀ i, Integral (x i)) : Integral (∏ i ∈ s, x i) :=
  Finset.prod_induction _ (fun y => Integral y) (fun _ _ h₁ h₂ => integral_mul h₁ h₂)
    integral_one fun i _ => hx i

end ExpansionsAtPlaces

open ExpansionsAtPlaces

end Formalism.InvariantFactorPaths.G7
