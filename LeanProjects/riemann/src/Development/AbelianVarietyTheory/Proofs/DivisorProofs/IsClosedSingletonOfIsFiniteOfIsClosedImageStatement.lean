import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedSingletonOfIsFiniteOfIsClosedImage
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosed_singleton_of_isFinite_of_isClosed_image : ∀ (X Z : Scheme.{0}) (f : X ⟶ Z), IsFinite f → ∀ x : X, IsClosed ({f x} : Set Z) → IsClosed ({x} : Set X) := by
  first | exact @GlobalTheory.isClosed_singleton_of_isFinite | exact GlobalTheory.isClosed_singleton_of_isFinite | (intros; apply GlobalTheory.isClosed_singleton_of_isFinite <;> assumption)
