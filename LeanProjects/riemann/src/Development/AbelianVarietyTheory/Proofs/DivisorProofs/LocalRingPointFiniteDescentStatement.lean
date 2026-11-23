import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingPointFiniteDescent
import Mathlib
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_ring_point_finite_descent : ∀ {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] {T : Type} [CommRing T] [IsLocalRing T] (v : Spec (CommRingCat.of T) ⟶ X), ∃ s : Finset T, ∀ (S : Type) [CommRing S] (φ : S →+* T), Function.Injective φ → (↑s : Set T) ⊆ Set.range φ → ∃ w : Spec (CommRingCat.of S) ⟶ X, Spec.map (CommRingCat.ofHom φ) ≫ w = v := by
  first | exact @GlobalTheory.spec_local_point_descends | exact GlobalTheory.spec_local_point_descends | (intros; apply GlobalTheory.spec_local_point_descends <;> assumption)
