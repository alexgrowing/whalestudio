import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftSemiPiBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftBaseChangeProdBijectiveSemilinearStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveLiftSemiOfSemilinearHomStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private def piSL {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {J : Type} {M M' : J → Type}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, AddCommGroup (M' i)]
    [∀ i, Module R' (M' i)] (f : ∀ i, M i →ₛₗ[σ] M' i) : (∀ i, M i) →ₛₗ[σ] (∀ i, M' i) where
  toFun x i := f i (x i)
  map_add' x y := by funext i; simp
  map_smul' r x := by funext i; simp [map_smulₛₗ]

private theorem piSL_bij {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {J : Type} [Finite J]
    {M M' : J → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, AddCommGroup (M' i)]
    [∀ i, Module R' (M' i)] (f : ∀ i, M i →ₛₗ[algebraMap R R'] M' i)
    (hf : ∀ i, Function.Bijective (liftSemi (f i))) : Function.Bijective (liftSemi (piSL f)) :=
  liftSemi_pi_bijective R R' J M M' f _ (fun _ _ ↦ rfl) hf

theorem liftSemi_pullTot1_bijective : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (C : Type) [Category.{0} C] [Finite C] [∀ T T' : C, Finite (T ⟶ T')] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} R') (α : ∀ T : C, F.obj T →+* F'.obj T) (hn : ∀ {T T' : C} (φ : T ⟶ T') (b : F.obj T), α T' (mp F φ b) = mp F' φ (α T b)) (hs : ∀ (T : C) (r : R) (b : F.obj T), α T (r • b) = algebraMap R R' r • α T b), (∀ (T : C) (f : F.obj T →ₛₗ[algebraMap R R'] F'.obj T), (∀ b, f b = α T b) → Function.Bijective (liftSemi f)) → Function.Bijective (liftSemi (pullTot1 (⟨𝟭 C, α, hn, hs⟩ : CoefMap (algebraMap R R') F F'))) := by
  intro R R' _ _ _ C _ _ _ F F' α hn hs h
  let a : ∀ T : C, F.obj T →ₛₗ[algebraMap R R'] F'.obj T := fun T ↦
    { toFun := α T, map_add' := map_add (α T), map_smul' := hs T }
  have ha : ∀ T, Function.Bijective (liftSemi (a T)) := fun T ↦ h T (a T) fun _ ↦ rfl
  have hsh : ∀ T, SemiHom (algebraMap R R') (α T) := fun T ↦
    semiHom_coef (⟨𝟭 C, α, hn, hs⟩ : CoefMap (algebraMap R R') F F') T
  refine GlobalTheory.T.liftBaseChange_prod_bijective_semilinear R R' _ _ _ _
    (piSL fun T : C ↦ piSL fun T' : C ↦ piSL fun _ : T ⟶ T' ↦ a T')
    (piSL fun T : C ↦ (hsh T).m1) _ (fun _ ↦ rfl) ?_ ?_
  · exact piSL_bij _ fun T ↦ piSL_bij _ fun T' ↦ piSL_bij _ fun _ ↦ ha T'
  · exact piSL_bij _ fun T ↦
      GlobalTheory.T.bijective_liftSemi_of_semilinear_hom R R' _ _ (α T) (hsh T) (a T) (fun _ ↦ rfl) (ha T)

end GlobalTheory
