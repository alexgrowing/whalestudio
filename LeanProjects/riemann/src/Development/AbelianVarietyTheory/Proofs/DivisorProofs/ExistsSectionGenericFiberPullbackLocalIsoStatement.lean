import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionGenericFiberPullbackLocalIso
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
theorem _root_.GlobalTheory.T.exists_section_generic_fiber_pullback_local_iso : ∀ (k K : Type) [CommRing k] [Field K] [Algebra k K] [IsFractionRing k K] (X G : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral G] [IsLocallyNoetherian G] (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (hp : IsPullback j q p (spMap (algebraMap k K))) (τ : K →+* ℂ), (∀ x, IsIso (j.stalkMap x)) → ∀ (M : MLine p (τ.comp (algebraMap k K))) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s), j (genericPoint G) = genericPoint X → ∃ (s' : (M.bc hp.w τ).B.Sec) (hs' : genericPoint G ∈ nonzeroLocus s'), nonzeroLocus s' = j ⁻¹ᵁ nonzeroLocus s ∧ (∀ x, (divOfSec (M.bc hp.w τ).φ.isLB s' hs').mult x = (divOfSec M.φ.isLB s hs).mult (j x)) ∧ ∀ y, (M.bc hp.w τ).logSec s' y = M.logSec s (bcPt hp.w τ y) := by
  first | exact @GlobalTheory.Mix.exists_sec_bc | exact GlobalTheory.Mix.exists_sec_bc | (intros; apply GlobalTheory.Mix.exists_sec_bc <;> assumption)
