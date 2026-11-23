import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EventuallySectionAndRelAmplePowDiv
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
theorem _root_.GlobalTheory.T.eventually_section_and_relAmple_pow_div : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M N : LB P.A.left), M.IsLB → N.IsLB → Out.RelAmple P.A M → ∀ᶠ t : ℕ in Filter.atTop, (∃ s : (LB.div (lbPow M t) N).Sec, ∃ j, s.f j ≠ 0) ∧ Out.RelAmple P.A (LB.div (lbPow M t) N) := by
  first | exact @GlobalTheory.AmpleDominates.eventually_sec_and_relAmple | exact GlobalTheory.AmpleDominates.eventually_sec_and_relAmple | (intros; apply GlobalTheory.AmpleDominates.eventually_sec_and_relAmple <;> assumption)
