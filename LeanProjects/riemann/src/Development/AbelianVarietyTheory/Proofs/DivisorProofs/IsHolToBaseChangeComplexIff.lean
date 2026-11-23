import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsHolToFibPtAndCompFibre

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory.PELU

theorem isHolTo_bc_iff : ∀ (R : Type) [CommRing R] (σ : R →+* ℂ) (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp ℂ)
    (f : X' ⟶ X), IsPullback f s' s (spMap σ) → ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (B : Set V)
    (y : V → (Sp ℂ ⟶ X')), (∀ b ∈ B, y b ≫ s' = spMap (RingHom.id ℂ)) →
    (IsHolTo B y ↔ IsHolTo B (fun b => y b ≫ f)) := by
  intro R _ σ X X' s s' f H V _ _ B y hy
  refine ⟨fun h => GlobalTheory.HolFibre.isHolTo_comp h f, fun h => ?_⟩
  have hB : IsOpen B := by
    have := (h ⊤ 0).1
    simpa using this
  refine GlobalTheory.HolFibre.isHolTo_of_isPullback H h ?_
  intro U g
  have hc := GlobalTheory.HolFibre.isHolTo_const (E := V) hB (spMap (RingHom.id ℂ)) U g
  have e : {b ∈ B | ⊤ ≤ (y b ≫ s') ⁻¹ᵁ U} = {b ∈ B | ⊤ ≤ (spMap (RingHom.id ℂ)) ⁻¹ᵁ U} := by
    ext b
    exact and_congr_right fun hb => by rw [hy b hb]
  rw [e]
  exact ⟨hc.1, hc.2.congr fun b hb => by simp only [hy b hb.1]⟩

end GlobalTheory.PELU
