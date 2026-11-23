import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.NormalisedBlowupCone
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace

namespace GlobalTheory

open Scheme.IdealSheafData in

theorem vanishingIdeal_comap_of_isOpenImmersion : ∀ (A X : Scheme.{0}) (g : A ⟶ X) [IsOpenImmersion g] (B : Closeds X) (B' : Closeds A), (∀ x : A, x ∈ B' ↔ g x ∈ B) → (Scheme.IdealSheafData.vanishingIdeal B).comap g = Scheme.IdealSheafData.vanishingIdeal B' := by
  intro A X g _ B B' h
  have hB : (vanishingIdeal B).support = B := by
    ext x
    simp
  have hr : (vanishingIdeal B).radical = vanishingIdeal B := by
    rw [← vanishingIdeal_support, hB]
  have hs : ((vanishingIdeal B).comap g).support = B' := by
    ext x
    simp [support_comap, h]
  rw [← hs, vanishingIdeal_support]
  ext U : 2
  rw [radical_ideal, ideal_comap_of_isOpenImmersion, ← Ideal.comap_radical, ← radical_ideal, hr]

end GlobalTheory
