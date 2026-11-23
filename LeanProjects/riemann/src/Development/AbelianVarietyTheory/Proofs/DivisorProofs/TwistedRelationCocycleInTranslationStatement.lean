import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedRelationCocycleInTranslation
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOneBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedRelation_cocycle_in_translation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (n j : ℤ) (ν mu β₀ β₁ β₂ : D.toPre.X) (s₀ : SecT D.toPre a n j β₀) (s₁ : SecT D.toPre a n j β₁) (s₂ : SecT D.toPre a n j β₂), β₁ = β₀ + shift h h' n j ν → β₂ = β₁ + shift h h' n j mu → TRel h ν s₀ s₁ → TRel h (ν + mu) s₀ s₂ → TRel h mu s₁ s₂ := by
  first | exact @GlobalTheory.TwFam.trel_cocycle | exact GlobalTheory.TwFam.trel_cocycle | (intros; apply GlobalTheory.TwFam.trel_cocycle <;> assumption)
