import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTransportedGeneratorDescendBijectiveApp
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntegralOfTorsion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_transported_generator_descend_bijective_app : ∀ {X X' Y Y' : Scheme.{0}} {K : Type} [Fintype K] {M : LB X} {L : LB X'} {F : X' ⟶ X} {w : LB.Iso L (M.pull F)}, PGen w → M.IsLB → L.IsLB → ∀ (π : Y' ⟶ Y), (∀ V : Y.Opens, Function.Bijective (π.app V).hom) → ∀ {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)}, (∀ k, φ' k ≫ F = π ≫ φ k) → ∀ {ε : K → ℤ} (a : LB.Gen (LB.LinComb L φ' ε)), a.IsGen → ∃ t : LB.Gen (LB.LinComb M φ ε), t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (I : (Z ⟶ X) → M.ι) (J : (Z ⟶ X') → L.ι), Good M z I → Good L z J → val t (r ≫ π) z I = (∏ k, gw w (r ≫ φ' k) z (I ((r ≫ φ' k) ≫ F)) (J (r ≫ φ' k)) ^ ε k) * val a r z J := by
  first | exact @GlobalTheory.Mum.BijDescent.exists_descend_bij | exact GlobalTheory.Mum.BijDescent.exists_descend_bij | (intros; apply GlobalTheory.Mum.BijDescent.exists_descend_bij <;> assumption)
