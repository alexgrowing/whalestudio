import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperOfInfinitelyManyLargeTorsionCounts
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_of_infinitely_many_large_torsion : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], GlobalTheory.SS.SmConn G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ C : ℕ, {m : ℕ | (m : k) ≠ 0 ∧ ∃ s : Finset (𝟙_ (Over (Sp k)) ⟶ G), (∀ x ∈ s, x ^ m = 1) ∧ m ^ (2 * g) ≤ C * s.card}.Infinite → IsProper G.hom := by
  first | exact @GlobalTheory.properOfInfinitelyManyLargeTorsionCounts | exact GlobalTheory.properOfInfinitelyManyLargeTorsionCounts | (intros; apply GlobalTheory.properOfInfinitelyManyLargeTorsionCounts <;> assumption)
