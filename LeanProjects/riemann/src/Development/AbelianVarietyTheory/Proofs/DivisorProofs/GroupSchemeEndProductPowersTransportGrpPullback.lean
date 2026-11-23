import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomProdPow
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

namespace GlobalTheory.ActFin

theorem prod_zpow_transport : ∀ (S S' : Scheme.{0}) (t : S' ⟶ S) (A : Over S) [GrpObj A] [IsCommMonObj A] (A' : Over S') [GrpObj A'] [IsCommMonObj A'] (φ : A'.left ⟶ A.left), IsGrpPullback A' A t φ → ∀ (r : ℕ) (g : Fin r → (A' ⟶ A')) (f : Fin r → (A ⟶ A)) (c : Fin r → ℤ), (∀ k, (g k).left ≫ φ = φ ≫ (f k).left) → (∏ k, g k ^ c k).left ≫ φ = φ ≫ (∏ k, f k ^ c k).left := by
  intro S S' t A _ _ A' _ _ φ h r g f c hc
  let U : Over.mk (A'.hom ≫ t) ⟶ A := pushPt h.1.w (𝟙 A')
  have hk : ∀ k, pushHom h A' (g k) = preHom U (f k) := fun k => by
    ext
    show (g k).left ≫ φ = (𝟙 A' : A' ⟶ A').left ≫ φ ≫ (f k).left
    rw [hc k, Over.id_left, Category.id_comp]
  have e : pushHom h A' (∏ k, g k ^ c k) = preHom U (∏ k, f k ^ c k) := by
    rw [map_prod, map_prod]
    exact Finset.prod_congr rfl fun k _ => by rw [map_zpow, map_zpow, hk k]
  have e' := congrArg (fun z => z.left) e
  change (∏ k, g k ^ c k).left ≫ φ = ((𝟙 A' : A' ⟶ A').left ≫ φ) ≫ (∏ k, f k ^ c k).left at e'
  rwa [Over.id_left, Category.id_comp] at e'

end GlobalTheory.ActFin
