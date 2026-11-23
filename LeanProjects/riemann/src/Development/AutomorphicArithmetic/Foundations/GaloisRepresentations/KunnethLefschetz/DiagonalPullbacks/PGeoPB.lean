import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.DiagonalPullbacks.ProjectiveBundleFormulaTorsion

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace UpperTheory.Gal.KunnethLefschetz.Di

section Sq
variable {C : Type*} [Category C] [HasPullbacks C]

private theorem sq_left {X Y B B' : C} (p : X ⟶ B) (q : Y ⟶ B) (s : B' ⟶ B) (u : X ⟶ Y) (hu : u ≫ q = p)
    (g : pullback p s ⟶ pullback q s) (e : g ≫ pullback.fst q s = pullback.fst p s ≫ u)
    (e' : g ≫ pullback.snd q s = pullback.snd p s) :
    IsPullback (pullback.fst p s) g u (pullback.fst q s) := by
  have outer : IsPullback (g ≫ pullback.snd q s) (pullback.fst p s) s (u ≫ q) := by
    rw [e', hu]
    exact (IsPullback.of_hasPullback p s).flip
  exact (IsPullback.of_right outer e (IsPullback.of_hasPullback q s).flip).flip

private theorem sq_right {X P B B' : C} (p : X ⟶ B) (q : P ⟶ B) (s : B' ⟶ B) (p₁ p₂ : P ⟶ X)
    (h₁ : p₁ ≫ p = q) (h : IsPullback p₁ p₂ p p) (g₁ g₂ : pullback q s ⟶ pullback p s)
    (e₁ : g₁ ≫ pullback.fst p s = pullback.fst q s ≫ p₁) (e₁' : g₁ ≫ pullback.snd p s = pullback.snd q s)
    (e₂ : g₂ ≫ pullback.fst p s = pullback.fst q s ≫ p₂) (e₂' : g₂ ≫ pullback.snd p s = pullback.snd q s) :
    IsPullback g₁ g₂ (pullback.snd p s) (pullback.snd p s) := by
  have A := sq_left q p s p₂ (h.w.symm.trans h₁) g₂ e₂ e₂'
  have outer := A.paste_horiz h
  rw [← e₁, pullback.condition] at outer
  exact IsPullback.of_right outer (e₁'.trans e₂'.symm) (IsPullback.of_hasPullback p s)

end Sq

theorem geoPB_holds : GeoPB := by
  intro K Ω _ _ _
  constructor
  · intro X Y p q u hu
    exact sq_left p q _ u hu _ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  · intro X P p q p₁ p₂ h₁ h₂ h
    exact sq_right p q _ p₁ p₂ h₁ h _ _ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

end UpperTheory.Gal.KunnethLefschetz.Di
