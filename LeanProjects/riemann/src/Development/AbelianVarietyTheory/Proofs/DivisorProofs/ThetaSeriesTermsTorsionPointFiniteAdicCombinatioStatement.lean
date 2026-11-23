import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesTermsTorsionPointFiniteAdicCombinatio
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeriesTerms_torsionPoint_finite_adic_combination : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (N : GlobalTheory.Ex.NumD (Kb R)) (ν : GlobalTheory.Ex.NumOf D.toPre (Kb R) N) (m : ℕ), Odd m → IsUnit (m : R) → ∀ (p : QkPt D.toPre (Kb R) (m ^ 2)) (q : N.QT (m ^ 2)), ν.QPt p q → ∃ (Jx : Type) (_ : Fintype Jx) (g : Jx → Kb R) (c : N.X → Jx → R), (∀ χ, N.txT m q χ = ∑ k, algebraMap (FractionRing R) (Kb R) (algebraMap R _ (c χ k)) * g k) ∧ ∀ n : ℕ, {χ | ¬ ∀ k, c χ k ∈ maximalIdeal R ^ n}.Finite := by
  first | exact @GlobalTheory.ThetaTermAdic.terms | exact GlobalTheory.ThetaTermAdic.terms | (intros; apply GlobalTheory.ThetaTermAdic.terms <;> assumption)
