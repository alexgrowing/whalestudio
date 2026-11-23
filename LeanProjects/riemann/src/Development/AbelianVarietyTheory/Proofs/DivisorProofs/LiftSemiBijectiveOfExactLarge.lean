import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FlatKerLarge

theorem liftSemi_bijective_of_exact {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
    [Module.Flat R R'] {Z M N Z' M' N' : Type*}
    [AddCommGroup Z] [Module R Z] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup Z'] [Module R' Z'] [AddCommGroup M'] [Module R' M'] [AddCommGroup N'] [Module R' N']
    (i : Z →ₗ[R] M) (d : M →ₗ[R] N) (i' : Z' →ₗ[R'] M') (d' : M' →ₗ[R'] N')
    (fZ : Z →ₛₗ[algebraMap R R'] Z') (fM : M →ₛₗ[algebraMap R R'] M')
    (fN : N →ₛₗ[algebraMap R R'] N')
    (hi : Function.Injective i) (hid : Function.Exact i d) (hi' : Function.Injective i')
    (hid' : Function.Exact i' d') (hZ : ∀ z, i' (fZ z) = fM (i z)) (hN : ∀ x, d' (fM x) = fN (d x))
    (hM : Function.Bijective (liftSemi fM)) (hNi : Function.Injective (liftSemi fN)) :
    Function.Bijective (liftSemi fZ) := by
  have sqZ : ∀ w, i' (liftSemi fZ w) = liftSemi fM (i.lTensor R' w) := fun w ↦ by
    induction w with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x z => rw [LinearMap.lTensor_tmul, liftSemi_tmul, liftSemi_tmul, map_smul, hZ]
  have sqN : ∀ w, d' (liftSemi fM w) = liftSemi fN (d.lTensor R' w) := fun w ↦ by
    induction w with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x z => rw [LinearMap.lTensor_tmul, liftSemi_tmul, liftSemi_tmul, map_smul, hN]
  have hinj : Function.Injective (i.lTensor R') :=
    Module.Flat.lTensor_preserves_injective_linearMap i hi
  have hex : Function.Exact (i.lTensor R') (d.lTensor R') := Module.Flat.lTensor_exact R' hid
  refine ⟨fun a b hab ↦ hinj (hM.1 ?_), fun z' ↦ ?_⟩
  · rw [← sqZ, ← sqZ, hab]
  · obtain ⟨m, hm⟩ := hM.2 (i' z')
    have h0 : d.lTensor R' m = 0 := hNi (by rw [← sqN, hm, hid'.apply_apply_eq_zero, map_zero])
    obtain ⟨w, rfl⟩ := (hex m).1 h0
    exact ⟨w, hi' (by rw [sqZ, hm])⟩

theorem liftSemi_bijective_of_exact_large : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R'] (Z : Type 1) [AddCommGroup Z] [Module R Z] (M : Type 1) [AddCommGroup M] [Module R M] (N : Type 1) [AddCommGroup N] [Module R N] (Z' : Type 1) [AddCommGroup Z'] [Module R' Z'] (M' : Type 1) [AddCommGroup M'] [Module R' M'] (N' : Type 1) [AddCommGroup N'] [Module R' N'] (i : Z →ₗ[R] M) (d : M →ₗ[R] N) (i' : Z' →ₗ[R'] M') (d' : M' →ₗ[R'] N') (fZ : Z →ₛₗ[algebraMap R R'] Z') (fM : M →ₛₗ[algebraMap R R'] M') (fN : N →ₛₗ[algebraMap R R'] N'), Function.Injective i → Function.Exact i d → Function.Injective i' → Function.Exact i' d' → (∀ z, i' (fZ z) = fM (i z)) → (∀ x, d' (fM x) = fN (d x)) → Function.Bijective (liftSemi fM) → Function.Injective (liftSemi fN) → Function.Bijective (liftSemi fZ) := by
  intro R R' _ _ _ _ Z _ _ M _ _ N _ _ Z' _ _ M' _ _ N' _ _ i d i' d' fZ fM fN hi hid hi' hid' hZ hN hM hNi
  exact liftSemi_bijective_of_exact i d i' d' fZ fM fN hi hid hi' hid' hZ hN hM hNi

end GlobalTheory.FlatKerLarge
