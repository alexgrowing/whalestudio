import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetFixingPointLocallyFiniteType
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.AV.GalPow

theorem exists_pow_card_of_finset {K L : Type} [Field K] [Fintype K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (σ : L ≃ₐ[K] L) (X : Finset L) :
    ∃ i : ℕ, ∀ x ∈ X, σ x = x ^ Fintype.card K ^ i := by
  let M := IntermediateField.adjoin K (X : Set L)
  have : FiniteDimensional K M := IntermediateField.finiteDimensional_adjoin fun x _ =>
    Algebra.IsIntegral.isIntegral x
  have : Finite M := Module.finite_of_finite K
  obtain ⟨i, hi⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow K M).2
    (σ.restrictNormal M)
  refine ⟨i, fun x hx => ?_⟩
  have h1 := AlgEquiv.restrictNormal_commutes σ M ⟨x, IntermediateField.subset_adjoin _ _ hx⟩
  rw [← hi] at h1
  dsimp only at h1
  rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate] at h1
  simpa using h1.symm

theorem exists_frob_pow_on_finset : ∀ (K : Type) [Field K] [Fintype K] (σ : Gal K) (X : Over (Sp K)) (s : Finset (ptOver K (AlgebraicClosure K) ⟶ X)), LocallyOfFiniteType X.hom → ∃ m : ℕ, ∀ x ∈ s, specAut σ ≫ x = specAut (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K) ^ m) ≫ x := by
  classical
  intro K _ _ σ X s hX
  set Φ := FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K) with hΦ
  have hF : ∀ x : ptOver K (AlgebraicClosure K) ⟶ X, ∃ t : Finset (AlgebraicClosure K), ∀ τ : Gal K,
      (∀ a ∈ t, τ a = a) → specAut τ ≫ x = x := fun x =>
    GlobalTheory.PtFin.exists_finset_fix K (AlgebraicClosure K) X hX x
  choose F hF using hF
  obtain ⟨i, hi⟩ := exists_pow_card_of_finset σ (s.biUnion F)
  have hΦi : ∀ a : AlgebraicClosure K, (Φ ^ i) a = a ^ Fintype.card K ^ i := fun a => by
    rw [AlgEquiv.coe_pow, hΦ, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
  refine ⟨i, fun x hx => ?_⟩
  set τ : Gal K := (Φ ^ i)⁻¹ * σ with hτ
  have hτfix : ∀ a ∈ F x, τ a = a := fun a ha => by
    have h1 := hi a (Finset.mem_biUnion.2 ⟨x, hx, ha⟩)
    rw [hτ, AlgEquiv.mul_apply, h1, ← hΦi]
    exact (Φ ^ i).symm_apply_apply a
  have hτx : specAut τ ≫ x = x := hF x τ hτfix
  have hσ : σ = Φ ^ i * τ := by rw [hτ, mul_inv_cancel_left]
  rw [hσ, specAut_mul, Category.assoc, hτx]

end GlobalTheory.AV.GalPow
