import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHolToBaseChangeComplexIff
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHolTo_baseChange_complex_iff : ∀ (R : Type) [CommRing R] (σ : R →+* ℂ) (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp ℂ) (f : X' ⟶ X), IsPullback f s' s (spMap σ) → ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (B : Set V) (y : V → (Sp ℂ ⟶ X')), (∀ b ∈ B, y b ≫ s' = spMap (RingHom.id ℂ)) → (IsHolTo B y ↔ IsHolTo B (fun b => y b ≫ f)) := by
  first | exact @GlobalTheory.PELU.isHolTo_bc_iff | exact GlobalTheory.PELU.isHolTo_bc_iff | (intros; apply GlobalTheory.PELU.isHolTo_bc_iff <;> assumption)
