import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.FibreScalar

theorem appLE_eq_of_eq {A Y : Scheme.{0}} {f g : A ⟶ Y} (h : f = g) (U : Y.Opens) (W : A.Opens)
    (e : W ≤ f ⁻¹ᵁ U) : f.appLE U W e = g.appLE U W (h ▸ e) := by
  subst h; rfl

theorem fromSpec_appLE_top {Y : Scheme.{0}} {U : Y.Opens} (hU : IsAffineOpen U) (e : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U) :
    hU.fromSpec.appLE U ⊤ e ≫ (Scheme.ΓSpecIso Γ(Y, U)).hom = 𝟙 _ := by
  rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, Category.assoc,
    ← Functor.map_comp_assoc]
  have : ((eqToHom hU.fromSpec_preimage_self).op ≫ (homOfLE e).op : Opposite.op _ ⟶ Opposite.op _) = 𝟙 _ :=
    Subsingleton.elim _ _
  rw [this, CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]

theorem specMap_appLE_top {A B : CommRingCat.{0}} (f : A ⟶ B) (e : (⊤ : (Spec B).Opens) ≤ Spec.map f ⁻¹ᵁ ⊤) :
    (Spec.map f).appLE ⊤ ⊤ e ≫ (Scheme.ΓSpecIso B).hom = (Scheme.ΓSpecIso A).hom ≫ f := by
  rw [← Scheme.ΓSpecIso_naturality]
  rfl

theorem spMap_chart_appLE_top {X : Scheme.{0}} (U : X.affineOpens) (m : Ideal Γ(X, U.1))
    (e : ⊤ ≤ (spMap (Ideal.Quotient.mk m) ≫ chart U) ⁻¹ᵁ U.1) :
    (spMap (Ideal.Quotient.mk m) ≫ chart U).appLE U.1 ⊤ e ≫
        (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U.1) ⧸ m))).hom =
      CommRingCat.ofHom (Ideal.Quotient.mk m) := by
  have e1 : (⊤ : (Sp Γ(X, U.1)).Opens) ≤ U.2.fromSpec ⁻¹ᵁ U.1 := U.2.fromSpec_preimage_self.ge
  have e2 : (⊤ : (Sp (Γ(X, U.1) ⧸ m)).Opens) ≤ spMap (Ideal.Quotient.mk m) ⁻¹ᵁ ⊤ := le_top
  have hk := fromSpec_appLE_top U.2 e1
  change (spMap (Ideal.Quotient.mk m) ≫ U.2.fromSpec).appLE U.1 ⊤ e ≫ _ = _
  have hk' : U.2.fromSpec.appLE U.1 ⊤ e1 ≫ (Scheme.ΓSpecIso (CommRingCat.of Γ(X, U.1))).hom = 𝟙 _ := hk
  rw [← Scheme.Hom.appLE_comp_appLE (spMap (Ideal.Quotient.mk m)) U.2.fromSpec _ ⊤ _ e1 e2, Category.assoc,
    specMap_appLE_top, ← Category.assoc, hk', Category.id_comp]

theorem fibre_scalar_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (m : Ideal Γ(X, U.1)) (A : Over (Sp (Γ(X, U.1) ⧸ m))) [GrpObj A] (ι : A.left ⟶ t.G.left), IsGrpPullback A t.G (spMap (Ideal.Quotient.mk m) ≫ chart U) ι → ∀ (O : t.G.left.Opens) (hO : O ≤ t.G.hom ⁻¹ᵁ U.1) (O' : A.left.Opens) (hO' : O' ≤ ι ⁻¹ᵁ O) (r : Γ(X, U.1)), r ∈ m → (ι.appLE O O' hO').hom ((t.G.hom.appLE U.1 O hO).hom r) = 0 := by
  intro E _ _ _ H X t U m A _ ι hpb O hO O' hO' r hr
  set g := spMap (Ideal.Quotient.mk m) ≫ chart U with hg
  have hw : ι ≫ t.G.hom = A.hom ≫ g := hpb.1.w
  have e5 : (⊤ : (Sp (Γ(X, U.1) ⧸ m)).Opens) ≤ g ⁻¹ᵁ U.1 := by
    intro x _
    change g x ∈ U.1
    rw [hg, Scheme.Hom.comp_apply]
    exact U.2.fromSpec_preimage_self.ge (Set.mem_univ _)
  have hz : (g.appLE U.1 ⊤ e5).hom r = 0 := by
    have h := congrArg (fun φ => φ.hom r) (spMap_chart_appLE_top U m e5)
    simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom, Ideal.Quotient.eq_zero_iff_mem.mpr hr] at h
    have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U.1) ⧸ m))).hom.hom :=
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U.1) ⧸ m))).hom).1
    exact hinj (h.trans (map_zero _).symm)
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, appLE_eq_of_eq hw,
    ← Scheme.Hom.appLE_comp_appLE A.hom g U.1 ⊤ O' e5 (fun x _ => trivial), CommRingCat.comp_apply, hz, map_zero]

end GlobalTheory.FibreScalar
