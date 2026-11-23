import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.InjTest
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.RepApi

open Polynomial UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.kerTest :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] {X : Type} (K : X → Type) [∀ x, CommRing (K x)] (f : ∀ x, A →+* K x)
    (ρ : ∀ x, G →* Matrix (Fin n) (Fin n) (K x)) (D : GDet n A G),
    (∀ a, (∀ x, f x a = 0) → a = 0) → (∀ x, D.map (f x) = GDet.ofRep (ρ x)) →
    ∀ y : MonoidAlgebra A G, (∀ x, GDet.repAlg (ρ x) (K x) (MonoidAlgebra.mapRingHom G (f x) y) = 0) → D.Kills y := by
  intro n A G _ _ X K _ f ρ D hf hD y hy
  refine (UpperTheory.V.AlgebraTools.Det.injTest K f hf).2 D y fun x => ?_
  rw [hD x]
  exact (UpperTheory.V.AlgebraTools.Det.repApi (ρ x)).2.2.2.2.1 _ (hy x)
