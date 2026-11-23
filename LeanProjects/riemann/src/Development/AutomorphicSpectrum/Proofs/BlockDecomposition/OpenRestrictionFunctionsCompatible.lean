import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowIdeal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectLeIffAffineSections
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalFunctions
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.RelSerreSections

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct Opposite

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.GE.RingCompat

attribute [local instance] algebraOfOver

lemma topIso_inv_res_hom {X : Scheme.{0}} (V : X.Opens) :
    X.presheaf.map (homOfLE le_top : V ⟶ ⊤).op ≫ V.topIso.inv = V.ι.appTop := by
  rw [Scheme.Opens.topIso_inv, Scheme.Hom.appTop, Scheme.Opens.ι_app]
  exact (X.presheaf.map_comp _ _).symm.trans (congrArg X.presheaf.map (Subsingleton.elim _ _))

lemma topIso_inv_res {X : Scheme.{0}} (V : X.Opens) (c : Γ(X, ⊤)) :
    V.topIso.inv (X.presheaf.map (homOfLE le_top : V ⟶ ⊤).op c) = V.ι.appTop c :=
  ConcreteCategory.congr_hom (topIso_inv_res_hom V) c

lemma appIso_hom_res {Z : Scheme.{0}} (O : Z.Opens) (W : (O : Scheme.{0}).Opens) (d : Γ(Z, ⊤)) :
    (O.ι.appIso W).hom (Z.presheaf.map (homOfLE le_top : O.ι ''ᵁ W ⟶ ⊤).op d) =
      (O : Scheme.{0}).presheaf.map (homOfLE le_top : W ⟶ ⊤).op (O.ι.appTop d) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, Scheme.Hom.appIso_hom',
    Scheme.Hom.map_appLE]
  rfl

lemma morphismRestrict_appTop_ι {X Z : Scheme.{0}} (φ : Z ⟶ X) (V : X.Opens) (c : Γ(X, ⊤)) :
    (φ ∣_ V).appTop (V.ι.appTop c) = (φ ⁻¹ᵁ V).ι.appTop (φ.appTop c) := by
  have h := congrArg Scheme.Hom.appTop (morphismRestrict_ι φ V)
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h
  exact ConcreteCategory.congr_hom h c

lemma overBase_appTop {X Z : Scheme.{0}} (φ : Z ⟶ X) (V : X.Opens) (hV : IsAffineOpen V)
    (b : Γ(X, V)) :
    (φ ∣_ V ≫ hV.isoSpec.hom).appTop ((Scheme.ΓSpecIso (.of Γ(X, V))).inv b) =
      (φ ∣_ V).appTop (V.topIso.inv b) := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, IsAffineOpen.isoSpec_hom_appTop,
    CommRingCat.comp_apply]
  erw [Iso.inv_hom_id_apply]

theorem toFunctions_preimage : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] {X Z : Scheme.{0}} [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] (φ : Z ⟶ X), φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ (V : X.Opens) (hV : IsAffineOpen V) [IsNoetherianRing Γ(X, V)], letI : (φ ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(X, V))) := ⟨φ ∣_ V ≫ hV.isoSpec.hom⟩; ∀ (W : (φ ⁻¹ᵁ V).toScheme.Opens) (a : A), ((φ ⁻¹ᵁ V).ι.appIso W).hom (toFunctions (A := A) ((φ ⁻¹ᵁ V).ι ''ᵁ W) a) = toFunctions (A := Γ(X, V)) W (toFunctions (A := A) V a) := by
  intro A _ _ X Z _ _ φ hφ V hV _ W a
  have hZ : (Z ↘ Spec (.of A)).appTop ((Scheme.ΓSpecIso (.of A)).inv a) =
      φ.appTop ((X ↘ Spec (.of A)).appTop ((Scheme.ΓSpecIso (.of A)).inv a)) := by
    rw [← hφ, Scheme.Hom.comp_appTop]
    rfl
  change ((φ ⁻¹ᵁ V).ι.appIso W).hom (Z.presheaf.map (homOfLE le_top).op
      ((Z ↘ Spec (.of A)).appTop ((Scheme.ΓSpecIso (.of A)).inv a))) =
    (φ ⁻¹ᵁ V).toScheme.presheaf.map (homOfLE le_top).op
      ((φ ∣_ V ≫ hV.isoSpec.hom).appTop ((Scheme.ΓSpecIso (.of Γ(X, V))).inv
        (X.presheaf.map (homOfLE le_top).op
          ((X ↘ Spec (.of A)).appTop ((Scheme.ΓSpecIso (.of A)).inv a)))))
  rw [overBase_appTop, topIso_inv_res, morphismRestrict_appTop_ι, hZ, appIso_hom_res]

end GlobalTheory.CompanionTheory.GE.RingCompat
