import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace GlobalTheory.PoincareDescent

theorem torsor_square {C : Type*} [Category C] [CartesianMonoidalCategory C] {A A' N : C} [GrpObj A] [GrpObj A']
    [GrpObj N] (i : N ⟶ A) (q : A ⟶ A') [IsMonHom q] (h : IsPullback i (toUnit N) q η[A']) :
    IsPullback (fst A N) (fst A N * (snd A N ≫ i)) q q := by
  have hiq : i ≫ q = 1 := by
    rw [h.w]; rfl
  have hdiff : ∀ {W : C} (x y : W ⟶ A), x ≫ q = y ≫ q → (x⁻¹ * y) ≫ q = toUnit W ≫ η[A'] := by
    intro W x y e
    rw [MonObj.mul_comp, GrpObj.inv_comp, e, inv_mul_cancel]; rfl
  refine ⟨⟨?_⟩, ⟨PullbackCone.IsLimit.mk _ (fun s ↦ lift s.fst (h.lift (s.fst⁻¹ * s.snd) (toUnit _)
      (hdiff _ _ s.condition))) (fun s ↦ lift_fst _ _) (fun s ↦ ?_) (fun s m h₁ h₂ ↦ ?_)⟩⟩
  · rw [MonObj.mul_comp, Category.assoc, hiq, MonObj.comp_one, _root_.mul_one]
  · rw [MonObj.comp_mul, lift_fst, lift_snd_assoc, h.lift_fst, mul_inv_cancel_left]
  · have e₁ : m ≫ fst A N = s.fst := h₁
    refine CartesianMonoidalCategory.hom_ext _ _ (by rw [e₁, lift_fst]) ?_
    rw [lift_snd]
    refine h.hom_ext ?_ (toUnit_unique _ _)
    rw [h.lift_fst, ← h₂, MonObj.comp_mul, e₁, Category.assoc, inv_mul_cancel_left]

end GlobalTheory.PoincareDescent
