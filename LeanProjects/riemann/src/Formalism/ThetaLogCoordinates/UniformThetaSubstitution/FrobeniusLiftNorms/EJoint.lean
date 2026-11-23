import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.StatementE
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.EntryDegree
import Formalism.GaussJetBounds.GaussJetProofs.ConstantCoeffAevalLinP

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral jetPair mfact)

namespace MinorFormHomogeneity

theorem coeff_subst_scale {K ι : Type} [Field K] (ϖ : K) (Th : MvPowerSeries ι K) (n : ι →₀ ℕ) :
    MvPowerSeries.coeff n (MvPowerSeries.subst
      (fun i => MvPowerSeries.C ϖ * (MvPowerSeries.X i : MvPowerSeries ι K)) Th) =
      ϖ ^ n.degree * MvPowerSeries.coeff n Th := by
  have h : (fun i => MvPowerSeries.C ϖ * (MvPowerSeries.X i : MvPowerSeries ι K)) =
      (fun _ : ι => ϖ) • (MvPowerSeries.X : ι → MvPowerSeries ι K) := by
    funext i
    simp [MvPowerSeries.smul_eq_C_mul]
  rw [h, ← MvPowerSeries.rescale_eq_subst, MvPowerSeries.coeff_rescale, Finsupp.prod,
    Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]

section Lin

variable {K : Type} [Field K] {ν r0 r1 : ℕ}

def Amat (TT : Finset (ZMod (2 * ν))) (ξ : ZMod (2 * ν) → Fin r0 → K) :
    TpV ν r1 ⊕ ZV ν r0 r1 → ZV ν r0 r1 → K
  | Sum.inl t, x => if t = (x.1, x.2.2) then (if x.1 ∈ TT then ξ x.1 x.2.1 else 0) else 0
  | Sum.inr y, x => if y = x then 1 else 0

end Lin

end MinorFormHomogeneity

end Formalism.InvariantFactorPaths.G7
