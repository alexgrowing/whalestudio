import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFunctorialMap

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

theorem lieModel_exists_unique_act : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R]
    (x : Spec (CommRingCat.of R) ⟶ S) (E : Type) [AddCommGroup E] [Module R E] (M : LieModel G x E)
    (O : Type) [CommRing O] (act : O → (G ⟶ G)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 G →
    (∀ a b, act (a * b) = act a ≫ act b) → (∀ a b, act (a + b) = act a * act b) →
    ∃! ρ : O →+* Module.End R E, M.IsActOf act ρ := by
  intro S G _ R _ x E _ _ M O _ act hmon h1 hmul hadd
  have hex : ∀ a, ∃ A : E →ₗ[R] E, (∀ e, M.pt (A e) = M.pt e ≫ act a) ∧
      ∀ B : E →ₗ[R] E, (∀ e, M.pt (B e) = M.pt e ≫ act a) → B = A := by
    intro a
    have := hmon a
    exact lieModel_exists_unique_diff S G G R x E E M M (act a)
  choose A hA hAu using hex
  have hone : LinearMap.id = A 1 := hAu 1 LinearMap.id fun e => by
    rw [h1, Category.comp_id]
    rfl
  have hmul' : ∀ a b, A (a * b) = A a * A b := fun a b => (hAu (a * b) (A a * A b) fun e => by
    rw [Module.End.mul_apply, hA a, hA b, Category.assoc, ← hmul b a, mul_comm]).symm
  have hadd' : ∀ a b, A (a + b) = A a + A b := fun a b => (hAu (a + b) (A a + A b) fun e => by
    rw [LinearMap.add_apply, M.add, hA a, hA b, ← MonObj.comp_mul, hadd]).symm
  refine ⟨RingHom.mk' { toFun := A, map_one' := hone.symm, map_mul' := hmul' } hadd',
    fun a e => hA a e, fun ρ hρ => ?_⟩
  ext a : 1
  exact hAu a (ρ a) (hρ a)

end GlobalTheory.CompanionTheory.Ar
