import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalTensorVanishingLocal
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_tensor_vanishing_local : ∀ (M : Scheme.{0}) (V W : M.Opens) (hW : IsAffineOpen W) (K : Type) [Field K],
    IsReduced (Γ(M, W) ⊗[ℤ] K) →
    (∀ q (hq : q ∈ minimalPrimes (Γ(M, W) ⊗[ℤ] K)),
      hW.fromSpec (PrimeSpectrum.comap (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := Γ(M, W)) (B := K)) ⟨q, hq.1.1⟩) ∈ V) →
    ∀ (h : Γ(M, W) ⊗[ℤ] K),
    (∀ (W' : M.Opens), IsAffineOpen W' → ∀ hW' : W' ≤ W ⊓ V,
      LinearMap.rTensor K (M.presheaf.map (homOfLE (hW'.trans inf_le_left)).op).hom.toAddMonoidHom.toIntLinearMap h = 0) →
    h = 0 := by
  first | exact @GlobalTheory.affine_restrictions_zero_of_minimalPrimes_over | exact GlobalTheory.affine_restrictions_zero_of_minimalPrimes_over | (intros; apply GlobalTheory.affine_restrictions_zero_of_minimalPrimes_over <;> assumption)
