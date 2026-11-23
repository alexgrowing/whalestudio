import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorRationalInjectivity
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_rational_injectivity : ∀ (N : ℕ) (I A : Type) [CommRing A] (B : I → Type) [∀ i, CommRing (B i)] (φ : ∀ i, A →+* B i),
    Module.Flat ℤ A → (∀ i, Module.Flat ℤ (B i)) → IsUnit ((N : ℤ) : A) →
    (N ≠ 0 → ∀ h : A ⊗[ℤ] ℚ, (∀ i, LinearMap.rTensor ℚ (φ i).toAddMonoidHom.toIntLinearMap h = 0) → h = 0) →
    (∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ h : A ⊗[ℤ] ZMod p,
      (∀ i, LinearMap.rTensor (ZMod p) (φ i).toAddMonoidHom.toIntLinearMap h = 0) → h = 0) →
    ∀ (L : Type) [AddCommGroup L] (h : A ⊗[ℤ] L),
      (∀ i, LinearMap.rTensor L (φ i).toAddMonoidHom.toIntLinearMap h = 0) → h = 0 := by
  first | exact @GlobalTheory.jointInj_tensor_of_rat_and_zmod | exact GlobalTheory.jointInj_tensor_of_rat_and_zmod | (intros; apply GlobalTheory.jointInj_tensor_of_rat_and_zmod <;> assumption)
