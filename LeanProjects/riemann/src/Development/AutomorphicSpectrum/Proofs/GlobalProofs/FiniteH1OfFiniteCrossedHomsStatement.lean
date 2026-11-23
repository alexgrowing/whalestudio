import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteH1OfFiniteCrossedHoms
import ReciprocityTheory.Hypotheses.GalCoh
import GroundTheory.ProfiniteCohomology.RestrictedRamification.IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import GroundTheory.ProfiniteCohomology.ContinuousCochains
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_H1_of_finite_crossed_homs : ∀ (k G : Type) [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (A : Rep.{0} k G) [IsDiscreteRep A], {f : G → A.V | IsLocallyConstant f ∧ ∀ g h : G, f (g * h) = f g + A.ρ g (f h)}.Finite → Finite (cohomology A 1) := by
  first | exact @GlobalTheory.CompanionTheory.Glob.finite_cohomology_one_of_finite_cocycles | exact GlobalTheory.CompanionTheory.Glob.finite_cohomology_one_of_finite_cocycles | (intros; apply GlobalTheory.CompanionTheory.Glob.finite_cohomology_one_of_finite_cocycles <;> assumption)
