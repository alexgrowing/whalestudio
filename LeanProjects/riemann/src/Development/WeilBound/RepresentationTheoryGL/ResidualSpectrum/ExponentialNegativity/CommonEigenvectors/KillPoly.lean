import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ExpNegGlue
import Development.WeilBound.SimpleEigenvalues.SimpleEigenvalueExtension.SimEig
import Development.AutomorphicArithmetic.AutomorphicVarieties.IntegralityNearIdentity.ExistsContDiffEventuallyEq
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PolynomialKilling.KillPoly4

noncomputable section

open Polynomial

namespace PositivityTheory.Rg.Rs.JKillPoly

def tr {G : Type} [Group G] (a : ℝ → G) (t : ℝ) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun F g := F (a t * g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end JKillPoly

open JKillPoly in
theorem killPoly_holds : KillPoly := KillingPolynomialDegreeFour.killPoly4

end PositivityTheory.Rg.Rs

end
