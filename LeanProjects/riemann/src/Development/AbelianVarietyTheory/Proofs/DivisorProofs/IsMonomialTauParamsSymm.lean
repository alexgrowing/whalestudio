import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsValueAtEqUnitMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTauLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonomialTauOfPerFactor
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

namespace GlobalTheory.MumFam

open InhTate

end GlobalTheory.MumFam

namespace GlobalTheory.MumFam

theorem monomial_eq_of_mul_unit {W : Type} [CommRing W] [Nontrivial W] {σ : Type} {P M : σ →₀ ℕ}
    {x x' : MvPowerSeries σ W} (hx : IsUnit x) (hx' : IsUnit x')
    (he : MvPowerSeries.monomial P (1 : W) * x = MvPowerSeries.monomial M 1 * x') : P = M := by
  have h1 : ∀ (P M : σ →₀ ℕ) (x x' : MvPowerSeries σ W), IsUnit x' →
      MvPowerSeries.monomial P (1 : W) * x = MvPowerSeries.monomial M 1 * x' → P ≤ M := by
    intro P M x x' hx' he
    have hc := congrArg (MvPowerSeries.coeff M) he
    rw [MvPowerSeries.coeff_monomial_mul, MvPowerSeries.coeff_monomial_mul, if_pos le_rfl, tsub_self,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at hc
    by_contra hPM
    rw [if_neg hPM, _root_.one_mul] at hc
    exact (hx'.map (MvPowerSeries.constantCoeff (σ := σ) (R := W))).ne_zero hc.symm
  exact le_antisymm (h1 _ _ _ _ hx' he) (h1 _ _ _ _ hx he.symm)

end GlobalTheory.MumFam

namespace GlobalTheory.MumFam

end GlobalTheory.MumFam

namespace GlobalTheory.MumFam

end GlobalTheory.MumFam
