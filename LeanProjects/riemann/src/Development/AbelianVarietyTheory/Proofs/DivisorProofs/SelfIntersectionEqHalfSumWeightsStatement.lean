import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionEqHalfSumWeights
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB

open GlobalTheory.Points ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.self_intersection_eq_half_sum_weights : ∀ (k : Type) [CommRing k] (k' : Type) [CommRing k'] [IsDomain k'] [Algebra k k'],
    IsArithVar (spMap (algebraMap k k')) 0 → ∀ (c : ∀ σ : k →+* ℂ, CxPts (spMap (algebraMap k k')) σ → ℝ)
    (hc : ∀ σ y, CxPts.CInfAt (c σ) y) (hcc : ∀ σ σ', (Weight.ofFun (c σ)).IsConj (Weight.ofFun (c σ'))) (a : ℝ),
    (fnB c hc hcc).IsSelfInter a → a = 1 / 2 * ∑ᶠ σ, ∑ᶠ y, c σ y := by
  first | exact @GlobalTheory.CurveSelf.isSelfInter_fnB_curve | exact GlobalTheory.CurveSelf.isSelfInter_fnB_curve | (intros; apply GlobalTheory.CurveSelf.isSelfInter_fnB_curve <;> assumption)
