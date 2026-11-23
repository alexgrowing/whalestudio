import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAffineOpenNonzeroLocusOfFibrewiseAmple
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.isAffineOpen_nonzeroLocus_of_fibrewise_ample : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (M : LB X) (d : ℕ) (m : ℕ) (u : Fin (m + 1) → LB.Sec (pw M d)), 1 ≤ d → IsProper f → M.IsLB → (⨆ i, Out.nonzeroLocus (u i) = ⊤) → (∀ q : Ideal R, q.IsPrime → ∃ (k : Type) (_ : Field k) (β : R →+* k), RingHom.ker β = q ∧ Out.RelAmple (Over.mk (pullback.snd f (spMap β))) (M.pull (pullback.fst f (spMap β)))) → ∀ i, IsAffineOpen (Out.nonzeroLocus (u i)) := by
  first | exact @GlobalTheory.FibreAmple.isAffineOpen_nonzeroLocus_of_fibres | exact GlobalTheory.FibreAmple.isAffineOpen_nonzeroLocus_of_fibres | (intros; apply GlobalTheory.FibreAmple.isAffineOpen_nonzeroLocus_of_fibres <;> assumption)
