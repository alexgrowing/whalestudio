import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Divisors.PreUMono
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageCochainRestrictionBijectiveClosedImmersiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocyclePullbackIffPreimageAffineHomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveDeformationAffineSectionsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

theorem exists_bock : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)), SmallExt t σ σ₀ → Flat s → ∀ x : HO1 s', ∃ z : HO2 s₀, Bock h.w h₀.w t x z := by
  intro R R' R₀ _ _ _ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ hS hF x
  have hc : IsClosedImmersion (spMap σ) := IsClosedImmersion.spec_of_surjective _ hS.1
  have hc₀ : IsClosedImmersion (spMap σ₀) := IsClosedImmersion.spec_of_surjective _ hS.2.2.1
  haveI : IsClosedImmersion φ := MorphismProperty.of_isPullback h.flip hc
  haveI : IsClosedImmersion φ₀ := MorphismProperty.of_isPullback h₀.flip hc₀
  have sec := fun U ↦ GlobalTheory.T.surjective_deformation_affine_sections R R' R₀ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ hS hF U
  have red := GlobalTheory.T.cocyclePullback_iff_preimage_affineHom R R' X X' s s' σ φ h.w
  have red₀ := GlobalTheory.T.cocyclePullback_iff_preimage_affineHom R R₀ X X₀ s s₀ σ₀ φ₀ h₀.w
  have bij₀ := (GlobalTheory.T.preimageCochainRestriction_bijective_closedImmersion R₀ X X₀ φ₀ s₀).2.1
  obtain ⟨c, hc⟩ := GlobalTheory.CatCoh.H1.mk_surjective _ ((preRes φ s').pull1 x)
  choose f hf using fun (U V : AffOp X) (a : U ⟶ V) ↦ (sec V).1 (c.1 U V a)
  have hd : ∀ (U V W : AffOp X) (a : U ⟶ V) (b : V ⟶ W), preα φ s s' W (d1 (OAff s) f U V W a b) = 0 := by
    intro U V W a b
    have nat := (preCoef h.w).naturality b (f U V a)
    have cc := c.2 a b
    rw [d1_apply, map_add, map_sub, hf, hf]
    erw [nat, hf]
    rw [cc]; ring
  choose w hw using fun (U V W : AffOp X) (a : U ⟶ V) (b : V ⟶ W) ↦ ((sec W).2.1 _).1 (hd U V W a b)
  have hdw : d1 (OAff s) f = t • w := by
    funext U V W a b; exact hw U V W a b
  have hw2 : ∀ ⦃U V W Y : AffOp X⦄ (a : U ⟶ V) (b : V ⟶ W) (e : W ⟶ Y),
      t • (mp (OAff s) e (w U V W a b) + w U W Y (a ≫ b) e - (w U V Y a (b ≫ e) + w V W Y b e)) = 0 := by
    intro U V W Y a b e
    have := (differential_one_mem_scaled_lattice (OAff s) f) a b e
    rw [hdw] at this
    simp only [Pi.smul_apply, map_smul] at this
    rw [smul_sub, smul_add, smul_add, this, sub_self]
  have hc0 : (fun U V W (a : U ⟶ V) (b : V ⟶ W) ↦ preα φ₀ s s₀ W (w U V W a b) : C2 (OPre φ₀ s₀)) ∈
      Z2 (OPre φ₀ s₀) := by
    intro U V W Y a b e
    have h1 := ((sec Y).2.2.2 _).2 (hw2 a b e)
    have nat := (preCoef h₀.w).naturality e (w U V W a b)
    simp only [map_add, map_sub] at h1
    erw [nat] at h1
    dsimp only
    exact sub_eq_zero.1 h1
  obtain ⟨z, hz⟩ := bij₀.2 (GlobalTheory.CatCoh.H2.mk _ ⟨_, hc0⟩)
  exact ⟨z, f, w, hdw, (red.1 f x).2 ⟨c, fun U V a ↦ (hf U V a).symm, hc⟩,
    (red₀.2.1 w z).2 ⟨⟨_, hc0⟩, fun U V W a b ↦ rfl, hz.symm⟩⟩

end GlobalTheory.AbCoh
