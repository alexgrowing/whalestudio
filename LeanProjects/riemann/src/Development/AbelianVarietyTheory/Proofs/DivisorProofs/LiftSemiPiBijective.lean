import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem liftSemi_pi_bijective : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (J : Type) [Finite J] (M M' : J → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, AddCommGroup (M' i)] [∀ i, Module R' (M' i)] (f : ∀ i, M i →ₛₗ[algebraMap R R'] M' i) (g : (∀ i, M i) →ₛₗ[algebraMap R R'] (∀ i, M' i)), (∀ x i, g x i = f i (x i)) → (∀ i, Function.Bijective (liftSemi (f i))) → Function.Bijective (liftSemi g) := by
  intro R R' _ _ _ J _ M M' _ _ _ _ f g hg hf
  classical
  haveI := Fintype.ofFinite J
  have key : ∀ y : R' ⊗[R] (∀ i, M i),
      liftSemi g y = Pi.map (fun i => liftSemi (f i)) (TensorProduct.piRight R R' R' M y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => funext i; simp [Pi.map]
    | tmul x m =>
      funext i
      simp [liftSemi_tmul, hg, TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]
    | add a b ha hb => rw [map_add, map_add, ha, hb]; funext i; simp
  have : (liftSemi g : R' ⊗[R] (∀ i, M i) → ∀ i, M' i)
      = Pi.map (fun i => liftSemi (f i)) ∘ (TensorProduct.piRight R R' R' M) := funext key
  rw [this]
  exact (Function.Bijective.piMap hf).comp (TensorProduct.piRight R R' R' M).bijective

end GlobalTheory
