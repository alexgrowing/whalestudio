import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFiberArithmeticVarietyIntegralProjective
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_fiber_arithmetic_variety_integral_projective : ∀ (k K : Type) [CommRing k] [Field K] [Algebra k K] [IsFractionRing k K] (X G : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (hp : IsPullback j q p (spMap (algebraMap k K))) (D : ℕ), IsArithVar p D → ∃ (_ : IsIntegral G) (_ : IsLocallyNoetherian G), IsProjOver q ∧ topologicalKrullDim G = D ∧ j (genericPoint G) = genericPoint X ∧ Function.Injective j ∧ (∀ x, IsIso (j.stalkMap x)) ∧ (∀ x, Order.coheight (j x) = Order.coheight x) ∧ ∀ z : X, z ∉ Set.range j → ∀ σ : k →+* ℂ, IsEmpty (CxPts (closι z ≫ p) σ) := by
  first | exact @GlobalTheory.Mix.genericFibre_facts | exact GlobalTheory.Mix.genericFibre_facts | (intros; apply GlobalTheory.Mix.genericFibre_facts <;> assumption)
