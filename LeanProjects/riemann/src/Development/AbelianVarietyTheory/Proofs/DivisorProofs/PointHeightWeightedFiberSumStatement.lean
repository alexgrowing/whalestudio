import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointHeightWeightedFiberSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedOfIsAlgPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointHeightDualAndLinearComb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightWeightRootChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsLgOfDetSymSubLe
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotMemPlaceholder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquidistributionAverageOverOrbit
import Development.AbelianVarietyTheory.Definitions.Divisors.DualRef
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB

open GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.point_height_weighted_fiber_sum : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y)
    (u : ∀ σ : 𝓞 F →+* ℂ, GlobalTheory.CxPts V.p σ → ℝ) (hu : ∀ σ y, GlobalTheory.CxPts.CInfAt (u σ) y)
    (hc : ∀ σ σ', (GlobalTheory.Weight.ofFun (u σ)).IsConj (GlobalTheory.Weight.ofFun (u σ'))) (w : V.G), IsClosed ({w} : Set V.G) →
    GlobalTheory.Published.ArExists →
    IsPtHt (fnB u hu hc) (V.j w)
      ((∑ᶠ σ, ∑ᶠ y ∈ {y : GlobalTheory.CxPts V.p σ | y.1 (IsLocalRing.closedPoint ℂ) = V.j w}, u σ y) /
        (2 * (Nat.card (V.X.residueField (V.j w) →+* ℂ) : ℝ))) := by
  first | exact @GlobalTheory.Mean4O.WeightHt.main | exact GlobalTheory.Mean4O.WeightHt.main | (intros; apply GlobalTheory.Mean4O.WeightHt.main <;> assumption)
