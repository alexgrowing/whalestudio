import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

namespace GlobalTheory

theorem fibre_restrict_scalar_compat : ∀ (X Z : Scheme.{0}) (p : Z ⟶ X) (U : X.affineOpens) (m : Ideal Γ(X, U.1)) (A : Scheme.{0}) (q : A ⟶ Sp (Γ(X, U.1) ⧸ m)) (ι : A ⟶ Z), ι ≫ p = q ≫ spMap (Ideal.Quotient.mk m) ≫ chart U → ∀ (V : Z.Opens) (hV : V ≤ p ⁻¹ᵁ U.1) (V' : A.Opens) (hV' : V' ≤ ι ⁻¹ᵁ V) (r : Γ(X, U.1)), (ι.appLE V V' hV').hom ((p.appLE U.1 V hV).hom r) = (q.appLE ⊤ V' le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U.1) ⧸ m))).inv.hom (Ideal.Quotient.mk m r)) := by
  intro X Z p U m A q ι h V hV V' hV' r
  have hU : IsAffineOpen U.1 := U.2
  have e0 : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U.1 := by
    rw [hU.fromSpec_preimage_self]
  have e1 : ⊤ ≤ (chart U) ⁻¹ᵁ U.1 := e0
  have k0 : hU.fromSpec.appLE U.1 ⊤ e0 ≫ (Scheme.ΓSpecIso Γ(X, U.1)).hom = 𝟙 _ := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, Category.assoc,
      ← Functor.map_comp_assoc]
    have : ((eqToHom hU.fromSpec_preimage_self).op ≫ (homOfLE e0).op : Opposite.op _ ⟶ Opposite.op _) = 𝟙 _ :=
      Subsingleton.elim _ _
    rw [this, CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]
  have k1 : ∀ x : Γ(X, U.1), ((chart U).appLE U.1 ⊤ e1).hom x = (Scheme.ΓSpecIso Γ(X, U.1)).inv.hom x := by
    intro x
    have := congrArg (fun f => (f ≫ (Scheme.ΓSpecIso Γ(X, U.1)).inv).hom x) k0
    simp only [CommRingCat.comp_apply, CommRingCat.id_apply, Iso.hom_inv_id_apply] at this
    exact this
  have kt : (spMap (Ideal.Quotient.mk m)).appLE ⊤ ⊤ le_top = (spMap (Ideal.Quotient.mk m)).appTop := by
    dsimp only [Scheme.Hom.appLE]
    exact (congrArg _ ((Sp (Γ(X, U.1) ⧸ m)).presheaf.map_id (Opposite.op ⊤))).trans (Category.comp_id _)
  have k2 : ∀ x : Γ(X, U.1), ((spMap (Ideal.Quotient.mk m)).appLE ⊤ ⊤ le_top).hom
      ((Scheme.ΓSpecIso Γ(X, U.1)).inv.hom x) =
      (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U.1) ⧸ m))).inv.hom (Ideal.Quotient.mk m x) := by
    intro x
    have hn := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk m))
    have := congrArg (fun f => f.hom x) hn
    simp only [CommRingCat.comp_apply] at this
    rw [kt]
    exact this.symm
  have hF : ⊤ ≤ (spMap (Ideal.Quotient.mk m) ≫ chart U) ⁻¹ᵁ U.1 :=
    (le_top : ⊤ ≤ spMap (Ideal.Quotient.mk m) ⁻¹ᵁ ⊤).trans
      ((TopologicalSpace.Opens.map (spMap (Ideal.Quotient.mk m)).base).map (homOfLE e1)).le
  have step : ∀ (g : A ⟶ X) (hg : g = q ≫ (spMap (Ideal.Quotient.mk m) ≫ chart U)) (e : V' ≤ g ⁻¹ᵁ U.1),
      (g.appLE U.1 V' e).hom r = (q.appLE ⊤ V' le_top).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U.1) ⧸ m))).inv.hom (Ideal.Quotient.mk m r)) := by
    rintro g rfl e
    rw [← Scheme.Hom.appLE_comp_appLE q (spMap (Ideal.Quotient.mk m) ≫ chart U) U.1 ⊤ V' hF le_top,
      ← Scheme.Hom.appLE_comp_appLE (spMap (Ideal.Quotient.mk m)) (chart U) U.1 ⊤ ⊤ e1 le_top]
    simp only [CommRingCat.comp_apply]
    rw [k1, k2]
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  exact step _ h _

end GlobalTheory
