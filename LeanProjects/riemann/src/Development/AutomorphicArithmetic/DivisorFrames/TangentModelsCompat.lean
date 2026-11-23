import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp
open scoped Classical

theorem UpperTheory.tangent_models_compat :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O₁ O₂ : Type) [CommRing O₁] [CommRing O₂] (β₁ : O₁ →+* c.F) (β₂ : O₂ →+* c.F) (Z₁ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β₁) (Z₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β₂) (R : Type) [CommRing R] (y : Sp R ⟶ Xo.XF c) (v₁ : Sp (DualNumber R) ⟶ Z₁.t.G.left) (v₂ : Sp (DualNumber R) ⟶ Z₂.t.G.left), Transp Z₁ Z₂ y v₁ v₂ → (∀ v₁' : Sp (DualNumber R) ⟶ Z₁.t.G.left, Transp Z₁ Z₂ y v₁' v₂ → v₁' = v₁) ∧ ∀ (R' : Type) [CommRing R'] (χ : R →+* R'), Transp Z₁ Z₂ (spMap χ ≫ y) (spMap (dualMap χ) ≫ v₁) (spMap (dualMap χ) ≫ v₂) := by
  intro E _ _ _ H Dw l Xo c O₁ O₂ _ _ β₁ β₂ Z₁ Z₂ R _ y v₁ v₂ h
  obtain ⟨w₁, w₂, h1, h2, h3, h4, h5⟩ := h
  refine ⟨?_, ?_⟩
  · rintro v₁' ⟨w₁', w₂', h1', h2', h3', h4', h5'⟩
    have e2 : w₂' = w₂ := Z₂.m.cart.1.hom_ext (h5'.trans h5.symm) (h2'.trans h2.symm)
    have e1 : w₁' = w₁ := Z₁.m0.toSABMap.cart.1.hom_ext (by rw [h3, h3', e2]) (h1'.trans h1.symm)
    rw [← h4, ← h4', e1]
  · intro R' _ χ
    have key : spMap (dualMap χ) ≫ spMap (algebraMap R (DualNumber R)) =
        spMap (algebraMap R' (DualNumber R')) ≫ spMap χ := by
      rw [ModelRelProbe.spMap_comp, ModelRelProbe.spMap_comp]
      congr 1
      ext s <;> simp [Formalism.L2.Pj.dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    refine ⟨spMap (dualMap χ) ≫ w₁, spMap (dualMap χ) ≫ w₂, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Category.assoc, h1, ← Category.assoc, key, Category.assoc]
    · rw [Category.assoc, h2, ← Category.assoc, key, Category.assoc]
    · rw [Category.assoc, h3, Category.assoc]
    · rw [Category.assoc, h4]
    · rw [Category.assoc, h5]
