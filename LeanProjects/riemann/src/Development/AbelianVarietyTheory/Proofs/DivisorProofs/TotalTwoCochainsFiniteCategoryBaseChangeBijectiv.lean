import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftSemiPiBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftBaseChangeProdBijectiveSemilinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveLiftSemiOfSemilinearHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveLiftSemiMOm
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TotTwoBaseChange

section Pi

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {J : Type} {M M' : J → Type}
  [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, AddCommGroup (M' i)] [∀ i, Module R' (M' i)]

def piSL (f : ∀ i, M i →ₛₗ[algebraMap R R'] M' i) : (∀ i, M i) →ₛₗ[algebraMap R R'] (∀ i, M' i) where
  toFun x i := f i (x i)
  map_add' x y := funext fun i ↦ map_add (f i) (x i) (y i)
  map_smul' r x := funext fun i ↦ map_smulₛₗ (f i) r (x i)

theorem piSL_bijective [Finite J] {f : ∀ i, M i →ₛₗ[algebraMap R R'] M' i}
    (hf : ∀ i, Function.Bijective (liftSemi (f i))) : Function.Bijective (liftSemi (piSL f)) :=
  liftSemi_pi_bijective R R' J M M' f (piSL f) (fun _ _ ↦ rfl) hf

end Pi

section Prod

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {M N M' N' : Type}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M'] [Module R' M'] [AddCommGroup N'] [Module R' N']

def prodSL (f : M →ₛₗ[algebraMap R R'] M') (g : N →ₛₗ[algebraMap R R'] N') :
    (M × N) →ₛₗ[algebraMap R R'] (M' × N') where
  toFun x := (f x.1, g x.2)
  map_add' x y := Prod.ext (map_add f x.1 y.1) (map_add g x.2 y.2)
  map_smul' r x := Prod.ext (map_smulₛₗ f r x.1) (map_smulₛₗ g r x.2)

theorem prodSL_bijective {f : M →ₛₗ[algebraMap R R'] M'} {g : N →ₛₗ[algebraMap R R'] N'}
    (hf : Function.Bijective (liftSemi f)) (hg : Function.Bijective (liftSemi g)) :
    Function.Bijective (liftSemi (prodSL f g)) :=
  liftSemi_prod_bijective R R' M N M' N' f g (prodSL f g) (fun _ ↦ rfl) hf hg

end Prod

theorem main : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (C : Type) [Category.{0} C] [Finite C] [∀ T T' : C, Finite (T ⟶ T')] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} R') (α : ∀ T : C, F.obj T →+* F'.obj T) (hn : ∀ {T T' : C} (φ : T ⟶ T') (b : F.obj T), α T' (mp F φ b) = mp F' φ (α T b)) (hs : ∀ (T : C) (r : R) (b : F.obj T), α T (r • b) = algebraMap R R' r • α T b), (∀ (T : C) (f : F.obj T →ₛₗ[algebraMap R R'] F'.obj T), (∀ b, f b = α T b) → Function.Bijective (liftSemi f)) → Function.Bijective (liftSemi (pullTot2 (⟨𝟭 C, α, hn, hs⟩ : CoefMap (algebraMap R R') F F'))) := by
  intro R R' _ _ _ C _ _ _ F F' α hn hs H
  let a : ∀ T : C, F.obj T →ₛₗ[algebraMap R R'] F'.obj T := fun T ↦
    { toFun := α T, map_add' := map_add _, map_smul' := hs T }
  have h : ∀ T : C, SemiHom (algebraMap R R') (α T) := hs
  have h0 : ∀ T, Function.Bijective (liftSemi (a T)) := fun T ↦ H T (a T) fun _ ↦ rfl
  have h1 : ∀ T, Function.Bijective (liftSemi (h T).m1) := fun T ↦
    GlobalTheory.kaehler_liftSemi_bijective R R' _ _ (α T) (h T) (a T) (fun _ ↦ rfl) (h0 T)
  have h2 : ∀ T, Function.Bijective (liftSemi ((h T).mOm 2)) := fun T ↦
    GlobalTheory.FormsBaseChange.bijective_liftSemi_mOm R R' _ _ (α T) (h T) (a T) (fun _ ↦ rfl) (h0 T) (h1 T) 2
  have k2 := piSL_bijective fun T : C ↦ piSL_bijective fun T' : C ↦ piSL_bijective fun T'' : C ↦
    piSL_bijective fun _ : T ⟶ T' ↦ piSL_bijective fun _ : T' ⟶ T'' ↦ h0 T''
  have k1 := piSL_bijective fun T : C ↦ piSL_bijective fun T' : C ↦
    piSL_bijective fun _ : T ⟶ T' ↦ h1 T'
  have k0 := piSL_bijective h2
  have k := prodSL_bijective k1 k0
  refine liftSemi_prod_bijective R R' (C2 F) (A1 F × W0 F 2) (C2 F') (A1 F' × W0 F' 2) _ _ _ ?_ k2 k
  intro x
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext T T' T'' φ ψ; exact cechDeRhamPullbackTotalDegreeTwo_function_part _ φ ψ x
  · funext T T' φ; exact pullTot2_a _ φ x
  · funext T; exact pullTot2_η _ x T

end GlobalTheory.TotTwoBaseChange
