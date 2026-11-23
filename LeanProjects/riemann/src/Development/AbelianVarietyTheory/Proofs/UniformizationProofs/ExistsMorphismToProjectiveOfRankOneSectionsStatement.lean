import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMorphismToProjectiveOfRankOneSections
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_morphism_to_projective_of_rank_one_sections : ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) (f : Z ⟶ Spec (CommRingCat.of R)) (H : LB Z) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ (X : Scheme.{0}) (f' : X ⟶ Spec (CommRingCat.of R)) (N : LB X) (m : ℕ) (w : Fin (n + 1) → Fin (m + 1) → LB.Sec N), N.IsLB → (⨆ i, ⨆ j, nonzeroLocus (w i j) = ⊤) → (∀ i i' j j' k, (w i j).f k * (w i' j').f k = (w i j').f k * (w i' j).f k) → (∀ (t : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → (∀ k, MvPolynomial.eval₂Hom (cst f (H.U k)) (fun i => (s i).f k) F = 0) → ∀ j k, MvPolynomial.eval₂Hom (cst f' (N.U k)) (fun i => (w i j).f k) F = 0) → ∃ φ : X ⟶ Z, φ ≫ f = f' ∧ ∀ (T : Scheme.{0}) (r : T ⟶ X) (ψ : T ⟶ Z), ψ ≫ f = r ≫ f' → (∀ z k k' i i' j, ψ z ∈ H.U k → r z ∈ N.U k' → gs ψ z (H.U k) ((s i).f k) * gs r z (N.U k') ((w i' j).f k') = gs ψ z (H.U k) ((s i').f k) * gs r z (N.U k') ((w i j).f k')) → r ≫ φ = ψ := by
  first | exact @GlobalTheory.RankMap.exists_hom_of_rank_one | exact GlobalTheory.RankMap.exists_hom_of_rank_one | (intros; apply GlobalTheory.RankMap.exists_hom_of_rank_one <;> assumption)
