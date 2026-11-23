import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.GalV

namespace UpperTheory.Gal.G3

private theorem splits_restrict (hS : SplitsPts) (hP : PtsOfSplits) {Z Y W W' : Scheme.{0}} (s : Y ⟶ Z) [IsFinite s] [Etale s]
    (c : W ⟶ Z) (J : Type) [Finite J] (σ : J → (W ⟶ Y)) (g : W' ⟶ W) (h : Splits s c σ) :
    Splits s (g ≫ c) fun j => g ≫ σ j := by
  have h0 := h
  obtain ⟨hc, -⟩ := h
  refine hS s (g ≫ c) J (fun j => g ≫ σ j) (fun j => by simp [hc j]) ?_
  intro Ω _ _ x y hy
  have hy' : y ≫ s = (x ≫ g) ≫ c := by simpa using hy
  obtain ⟨j, hj, huniq⟩ := hP s c J σ h0 Ω (x ≫ g) y hy'
  exact ⟨j, by simpa using hj, fun i hi => huniq i (by simpa using hi)⟩

private theorem splits_down (hS : SplitsPts) (hP : PtsOfSplits) {P Y Z' Z W : Scheme.{0}} {v : P ⟶ Y} {s' : P ⟶ Z'} {s : Y ⟶ Z}
    {g : Z' ⟶ Z} [IsFinite s] [Etale s] (sq : IsPullback v s' s g) (c : W ⟶ Z') (J : Type) [Finite J] (σ : J → (W ⟶ P))
    (hσ : ∀ j, σ j ≫ s' = c) (h : Splits s' c σ) : Splits s (c ≫ g) fun j => σ j ≫ v := by
  refine hS s (c ≫ g) J (fun j => σ j ≫ v)
    (fun j => by rw [Category.assoc, sq.w, ← Category.assoc, hσ j]) ?_
  intro Ω _ _ x y hy
  have hw : y ≫ s = (x ≫ c) ≫ g := by simpa using hy
  obtain ⟨j, hj, huniq⟩ := hP s' c J σ h Ω x (sq.lift y (x ≫ c) hw) (by simp)
  refine ⟨j, ?_, ?_⟩
  · simp only
    rw [← Category.assoc, hj, sq.lift_fst]
  · intro i hi
    apply huniq
    apply sq.hom_ext
    · simpa using hi
    · simp [hσ i]

private theorem splits_up (hS : SplitsPts) (hP : PtsOfSplits) {P Y Z' Z W : Scheme.{0}} {v : P ⟶ Y} {s' : P ⟶ Z'} {s : Y ⟶ Z}
    {g : Z' ⟶ Z} [IsFinite s] [Etale s] (sq : IsPullback v s' s g) (c : W ⟶ Z') (J : Type) [Finite J] (σ : J → (W ⟶ P))
    (hσ : ∀ j, σ j ≫ s' = c) (h : Splits s (c ≫ g) fun j => σ j ≫ v) : Splits s' c σ := by
  have : IsFinite s' := MorphismProperty.of_isPullback (P := @IsFinite) sq ‹_›
  have : Etale s' := MorphismProperty.of_isPullback (P := @Etale) sq ‹_›
  refine hS s' c J σ hσ ?_
  intro Ω _ _ x y hy
  have hw : (y ≫ v) ≫ s = x ≫ c ≫ g := by
    rw [Category.assoc, sq.w, ← Category.assoc, hy, Category.assoc]
  obtain ⟨j, hj, huniq⟩ := hP s (c ≫ g) J (fun j => σ j ≫ v) h Ω x (y ≫ v) hw
  refine ⟨j, ?_, ?_⟩
  · apply sq.hom_ext
    · simpa using hj
    · simp [hσ j, hy]
  · intro i hi
    apply huniq
    rw [← Category.assoc, hi]

theorem pSplitsBasic : SplitsPts → PtsOfSplits → SplitsBasic := fun hS hP =>
  ⟨fun s _ _ c J _ σ g h => splits_restrict hS hP s c J σ g h,
   fun _ _ _ _ _ _ sq c J _ σ hσ => ⟨splits_down hS hP sq c J σ hσ, splits_up hS hP sq c J σ hσ⟩⟩

end UpperTheory.Gal.G3

end
