import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.PhiPow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsFamRep
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ZeroFLeftExt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullTopZFConstUnit

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.InhTate ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.PhiPowerTest

open ToricData

abbrev qq : ℤ → (FractionRing InhTate.R)ˣ := fun n => piK ^ (n ^ 2)

def multData : DegData InhTate.R InhTate.I where
  toPre := toricPre InhTate.R ℤ qq
  psi_even := toricPre_tate ▸ tateData.psi_even
  tau_bimult := toricPre_tate ▸ tateData.tau_bimult
  psi_pos := toricPre_tate ▸ tateData.psi_pos
  psi_tendsto := toricPre_tate ▸ tateData.psi_tendsto

abbrev KK : Type := FractionRing InhTate.R

def halfPeriod : QkPt multData.toPre KK 2 :=
  ⟨(1 : ℤ), pt qq KK (zpowersHom _ piK), pt qq KK (zpowersHom _ piK ^ 2), (isNsmul_pt qq KK 2 _ _).2 rfl,
    (isIota_pt qq KK _ _).2 fun χ => by
      rw [polar_zpow_sq]
      change (((piK ^ χ) ^ 2 : KKˣ) : KK) = ((piK ^ (2 * 1 * χ) : KKˣ) : KK)
      rw [← zpow_natCast, ← zpow_mul, mul_one, mul_comm]
      rfl⟩

def normOne : LB.Gen (LB.LinComb multData.toPre.P.L (DegPre.lineφ multData.toPre KK halfPeriod.g.b) (DegPre.lineε 2)) :=
  cg _ _ (Geo.Tor.unitOn (1 : KKˣ))

end GlobalTheory.PhiPowerTest
