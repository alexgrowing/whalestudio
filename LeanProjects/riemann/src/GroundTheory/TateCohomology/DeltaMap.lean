import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory groupCohomology Rep

universe u

variable {k G H : Type u} [CommRing k] [Group G] [Group H]

noncomputable def cochainsMapShortComplex (f : G →* H) {X : ShortComplex (Rep k H)}
    {Y : ShortComplex (Rep k G)} (F : X.map (resFunctor f) ⟶ Y) :
    X.map (cochainsFunctor k H) ⟶ Y.map (cochainsFunctor k G) where
  τ₁ := cochainsMap f F.τ₁
  τ₂ := cochainsMap f F.τ₂
  τ₃ := cochainsMap f F.τ₃
  comm₁₂ := by
    ext n x
    refine funext fun g => ?_
    exact congrArg (fun φ => φ.hom (x (f ∘ g))) F.comm₁₂
  comm₂₃ := by
    ext n x
    refine funext fun g => ?_
    exact congrArg (fun φ => φ.hom (x (f ∘ g))) F.comm₂₃

theorem δ_comp_map (f : G →* H) {X : ShortComplex (Rep k H)} {Y : ShortComplex (Rep k G)}
    (hX : X.ShortExact) (hY : Y.ShortExact) (F : X.map (resFunctor f) ⟶ Y)
    (i j : ℕ) (hij : i + 1 = j) :
    δ hX i j hij ≫ map f F.τ₁ j = map f F.τ₃ i ≫ δ hY i j hij :=
  HomologicalComplex.HomologySequence.δ_naturality (cochainsMapShortComplex f F)
    (map_cochainsFunctor_shortExact hX) (map_cochainsFunctor_shortExact hY) i j hij

theorem δ_comp_map_res (f : G →* H) {X : ShortComplex (Rep k H)} (hX : X.ShortExact)
    (i j : ℕ) (hij : i + 1 = j) :
    δ hX i j hij ≫ map f (𝟙 (res f X.X₁)) j =
      map f (𝟙 (res f X.X₃)) i ≫ δ ((shortExact_res f).2 hX) i j hij :=
  δ_comp_map f hX ((shortExact_res f).2 hX) (𝟙 _) i j hij

end GroundTheory.GroupCoh
