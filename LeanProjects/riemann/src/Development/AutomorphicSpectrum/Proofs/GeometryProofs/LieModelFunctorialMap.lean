import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

theorem IsTanAt.comp_monHom {S : Scheme.{0}} {G G' : Over S} [GrpObj G] [GrpObj G'] {R : Type} [CommRing R]
    {x : Spec (CommRingCat.of R) ⟶ S} {v : epsAt x ⟶ G} (hv : IsTanAt G x v) (f : G ⟶ G') [IsMonHom f] :
    IsTanAt G' x (v ≫ f) := by
  unfold IsTanAt at hv ⊢
  rw [Over.comp_left, ← Category.assoc, hv, ← Over.comp_left, MonObj.one_comp]

theorem lieModel_exists_unique_diff :
    ∀ (S : Scheme.{0}) (G G' : Over S) [GrpObj G] [GrpObj G'] (R : Type) [CommRing R]
      (x : Spec (CommRingCat.of R) ⟶ S) (E E' : Type) [AddCommGroup E] [Module R E] [AddCommGroup E']
      [Module R E'] (M : LieModel G x E) (M' : LieModel G' x E') (f : G ⟶ G') [IsMonHom f],
      ∃! A : E →ₗ[R] E', ∀ e, M'.pt (A e) = M.pt e ≫ f := by
  intro S G G' _ _ R _ x E E' _ _ _ _ M M' f _
  have hex : ∀ e, ∃ e', M'.pt e' = M.pt e ≫ f := fun e => M'.onto _ ((M.tan e).comp_monHom f)
  choose A hA using hex
  have hadd : ∀ e₁ e₂, A (e₁ + e₂) = A e₁ + A e₂ := fun e₁ e₂ => M'.inj (by
    rw [hA, M'.add, hA, hA, M.add, MonObj.mul_comp])
  have hsmul : ∀ (c : R) e, A (c • e) = c • A e := fun c e => M'.inj (by
    rw [hA]
    apply Over.OverMorphism.ext
    rw [M'.smul, hA, Over.comp_left, Over.comp_left, M.smul, Category.assoc])
  refine ⟨⟨⟨A, hadd⟩, hsmul⟩, fun e => hA e, ?_⟩
  intro B hB
  ext e
  exact M'.inj ((hB e).trans (hA e).symm)

end GlobalTheory.CompanionTheory.Ar
