import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismTrivialOnReducedKernel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.morphism_trivial_on_reduced_kernel : ∀ (A Y Y' Z : Over (Sp ℂ)) [GrpObj A] [GrpObj Y] [GrpObj Y'] [IsSeparated Y'.hom] (u : A ⟶ Y) (f : A ⟶ Y')
    (i : Z ⟶ A), IsPullback i (toUnit Z) u η[Y] → ∀ [AlgebraicGeometry.IsReduced Z.left] [LocallyOfFiniteType Z.hom],
    (∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, x ≫ u = 1 → x ≫ f = 1) →
    ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), x ≫ u = 1 → x ≫ f = 1 := by
  first | exact @GlobalTheory.KernelKill.comp_eq_one_of_kill_closedPoints | exact GlobalTheory.KernelKill.comp_eq_one_of_kill_closedPoints | (intros; apply GlobalTheory.KernelKill.comp_eq_one_of_kill_closedPoints <;> assumption)
