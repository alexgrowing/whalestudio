import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Divisors.PreUMono
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatLiftingObstructionClassStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftOfLiftingObstructionEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftingObstructionBocksteinAddStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ObstructionClassNaturalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackProdSelfIsPullbackStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem pullHO1_surjective_of_smallExt : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (g : ℕ) (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp R')) [GrpObj A'] (A₀ : Over (Sp R₀)) [GrpObj A₀] (φ : A'.left ⟶ A.left) (φ₀ : A₀.left ⟶ A.left) (h : IsGrpPullback A' A (spMap σ) φ) (h₀ : IsGrpPullback A₀ A (spMap σ₀) φ₀), SmallExt t σ σ₀ → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → StructureSheafH1Primitive A' → NoPrimitiveStructureSheafH2 A₀ → Function.Surjective (pullHO1 h.1.w) := by
  intro R R' R₀ _ _ _ t σ σ₀ g A _ A' _ A₀ _ φ φ₀ h h₀ hS hA _ hP hN x
  haveI := hA.smooth
  have hF : Flat A.hom := inferInstance
  have hF2 : Flat (A ⊗ A).hom := by
    show Flat (pullback.fst A.hom A.hom ≫ A.hom)
    infer_instance
  obtain ⟨Φ, hΦ, hm, h1, h2, -, -⟩ := GlobalTheory.T.grpPullback_prod_self_isPullback R R' σ A A' φ h
  obtain ⟨Φ₀, hΦ₀, hm₀, h1₀, h2₀, -, -⟩ := GlobalTheory.T.grpPullback_prod_self_isPullback R R₀ σ₀ A A₀ φ₀ h₀
  obtain ⟨z, hz⟩ := GlobalTheory.T.exists_flat_lifting_obstruction_class R R' R₀ t σ σ₀ A.left A'.left A₀.left A.hom A'.hom A₀.hom φ φ₀ h.1 h₀.1 hS hF x

  have nat : ∀ (ψ : (A ⊗ A).left ⟶ A.left) (ψ' : (A' ⊗ A').left ⟶ A'.left) (ψ₀ : (A₀ ⊗ A₀).left ⟶ A₀.left)
      (w : ψ ≫ A.hom = (A ⊗ A).hom ≫ spMap (RingHom.id R)) (w' : ψ' ≫ A'.hom = (A' ⊗ A').hom ≫ spMap (RingHom.id R'))
      (w₀ : ψ₀ ≫ A₀.hom = (A₀ ⊗ A₀).hom ≫ spMap (RingHom.id R₀)), ψ' ≫ φ = Φ ≫ ψ → ψ₀ ≫ φ₀ = Φ₀ ≫ ψ →
      ∀ z', Bock hΦ.w hΦ₀.w t (pullHO1 w' x) z' → z' = pullHO2 w₀ z := by
    intro ψ ψ' ψ₀ w w' w₀ e e₀ z' hz'
    exact GlobalTheory.T.obstructionClass_natural R R' R₀ t σ σ₀ A.left A'.left A₀.left A.hom A'.hom A₀.hom φ φ₀ h.1 h₀.1
      (A ⊗ A).left (A' ⊗ A').left (A₀ ⊗ A₀).left (A ⊗ A).hom (A' ⊗ A').hom (A₀ ⊗ A₀).hom Φ Φ₀ hΦ hΦ₀
      ψ ψ' ψ₀ w w' w₀ e e₀ hS hF hF2 x z z' hz hz'
  have ex : ∀ y : HO1 (A' ⊗ A').hom, ∃ z' : HO2 (A₀ ⊗ A₀).hom, Bock hΦ.w hΦ₀.w t y z' := fun y ↦
    GlobalTheory.T.exists_flat_lifting_obstruction_class R R' R₀ t σ σ₀ (A ⊗ A).left (A' ⊗ A').left (A₀ ⊗ A₀).left (A ⊗ A).hom (A' ⊗ A').hom (A₀ ⊗ A₀).hom
      Φ Φ₀ hΦ hΦ₀ hS hF2 y
  obtain ⟨z1, hz1⟩ := ex (pO1 (fst A' A') x)
  obtain ⟨z2, hz2⟩ := ex (pO1 (snd A' A') x)
  have e1 : z1 = structureSheafH2Pullback (fst A₀ A₀) z := nat _ _ _ (ovw (fst A A)) (ovw (fst A' A')) (ovw (fst A₀ A₀)) h1 h1₀ z1 hz1
  have e2 : z2 = structureSheafH2Pullback (snd A₀ A₀) z := nat _ _ _ (ovw (snd A A)) (ovw (snd A' A')) (ovw (snd A₀ A₀)) h2 h2₀ z2 hz2
  have hsum := GlobalTheory.T.liftingObstructionBockstein_add R R' R₀ t σ σ₀ (A ⊗ A).left (A' ⊗ A').left (A₀ ⊗ A₀).left (A ⊗ A).hom (A' ⊗ A').hom
    (A₀ ⊗ A₀).hom Φ Φ₀ hΦ.w hΦ₀.w _ _ z1 z2 hz1 hz2
  rw [← hP x] at hsum
  have em : z1 + z2 = structureSheafH2Pullback μ[A₀] z := nat _ _ _ (ovw μ[A]) (ovw μ[A']) (ovw μ[A₀]) hm hm₀ _ hsum
  have z0 : z = 0 := hN z (by rw [← em, e1, e2])
  subst z0
  exact GlobalTheory.T.exists_lift_of_lifting_obstruction_eq_zero R R' R₀ t σ σ₀ A.left A'.left A₀.left A.hom A'.hom A₀.hom φ φ₀ h.1 h₀.1 hS hF x hz

end GlobalTheory.AbCoh
