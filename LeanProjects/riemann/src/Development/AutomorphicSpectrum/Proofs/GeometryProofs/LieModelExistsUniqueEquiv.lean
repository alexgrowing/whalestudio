import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem lieModel_existsUnique_equiv :
    ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S) (E E' : Type) [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R E'] (M : LieModel G x E) (M' : LieModel G x E'), ∃! f : E ≃ₗ[R] E', ∀ e, M'.pt (f e) = M.pt e := by
  intro S G _ R _ x E E' _ _ _ _ M M'

  choose f hf using fun e => M'.onto (M.pt e) (M.tan e)
  choose g hg using fun e' => M.onto (M'.pt e') (M'.tan e')
  let φ : E ≃ₗ[R] E' :=
    { toFun := f
      invFun := g
      map_add' := fun e e' => M'.inj (by rw [M'.add, hf, hf, hf, M.add])
      map_smul' := fun c e => by
        show f (c • e) = c • f e
        apply M'.inj
        apply Over.OverMorphism.ext
        rw [M'.smul, hf, hf, M.smul]
      left_inv := fun e => M.inj (by rw [hg, hf])
      right_inv := fun e' => M'.inj (by rw [hf, hg]) }
  refine ⟨φ, fun e => hf e, fun ψ hψ => ?_⟩
  exact LinearEquiv.ext fun e => M'.inj ((hψ e).trans (hf e).symm)

end GlobalTheory.CompanionTheory.Ar
