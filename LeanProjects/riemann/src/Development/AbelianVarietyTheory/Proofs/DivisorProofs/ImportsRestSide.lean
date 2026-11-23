import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KerFlat

theorem main : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R'] (Z : Type) [AddCommGroup Z] [Module R Z] (M : Type) [AddCommGroup M] [Module R M] (N : Type) [AddCommGroup N] [Module R N] (Z' : Type) [AddCommGroup Z'] [Module R' Z'] (M' : Type) [AddCommGroup M'] [Module R' M'] (N' : Type) [AddCommGroup N'] [Module R' N'] (i : Z →ₗ[R] M) (d : M →ₗ[R] N) (i' : Z' →ₗ[R'] M') (d' : M' →ₗ[R'] N') (fZ : Z →ₛₗ[algebraMap R R'] Z') (fM : M →ₛₗ[algebraMap R R'] M') (fN : N →ₛₗ[algebraMap R R'] N'), Function.Injective i → Function.Exact i d → Function.Injective i' → Function.Exact i' d' → (∀ z, i' (fZ z) = fM (i z)) → (∀ x, d' (fM x) = fN (d x)) → Function.Bijective (liftSemi fM) → Function.Injective (liftSemi fN) → Function.Bijective (liftSemi fZ) := by
  intro R R' _ _ _ _ Z _ _ M _ _ N _ _ Z' _ _ M' _ _ N' _ _ i d i' d' fZ fM fN hi hid hi' hid' ci cd hM hN
  have c1 : ∀ x : R' ⊗[R] Z, i' (liftSemi fZ x) = liftSemi fM (LinearMap.lTensor R' i x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul r z => simp only [liftSemi_tmul, LinearMap.lTensor_tmul, map_smul, ci]
  have c2 : ∀ x : R' ⊗[R] M, d' (liftSemi fM x) = liftSemi fN (LinearMap.lTensor R' d x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul r m => simp only [liftSemi_tmul, LinearMap.lTensor_tmul, map_smul, cd]
  have hiB : Function.Injective (LinearMap.lTensor R' i) :=
    Module.Flat.lTensor_preserves_injective_linearMap i hi
  have hex : Function.Exact (LinearMap.lTensor R' i) (LinearMap.lTensor R' d) :=
    Module.Flat.lTensor_exact R' hid
  refine ⟨fun x y hxy => hiB (hM.1 ?_), fun z' => ?_⟩
  · rw [← c1, ← c1, hxy]
  · obtain ⟨y, hy⟩ := hM.2 (i' z')
    have h0 : LinearMap.lTensor R' d y = 0 := by
      apply hN
      rw [← c2, hy, map_zero]
      exact (hid' (i' z')).2 ⟨z', rfl⟩
    obtain ⟨x, rfl⟩ := (hex y).1 h0
    exact ⟨x, hi' (by rw [c1, hy])⟩

end GlobalTheory.KerFlat
