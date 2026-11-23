import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEigen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.DescGen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.EigenDescent
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.EigenDescent

theorem topIso_inv_eq_appLE {X : Scheme.{0}} (W : X.Opens) (h : (⊤ : W.toScheme.Opens) ≤ W.ι ⁻¹ᵁ W) :
    W.topIso.inv = W.ι.appLE W ⊤ h :=
  (Scheme.Opens.topIso_inv W).trans (Eq.trans rfl (Scheme.Opens.ι_appLE W W ⊤ h).symm)

theorem topIso_inv_appTop {X Z : Scheme.{0}} (W : X.Opens) (y : Z ⟶ W.toScheme)
    (h : (⊤ : Z.Opens) ≤ (y ≫ W.ι) ⁻¹ᵁ W) :
    W.topIso.inv ≫ y.appTop = (y ≫ W.ι).appLE W ⊤ h := by
  have h0 : (⊤ : W.toScheme.Opens) ≤ W.ι ⁻¹ᵁ W := fun x _ => x.2
  rw [topIso_inv_eq_appLE W h0]
  refine Eq.trans ?_ (Scheme.Hom.appLE_comp_appLE y W.ι W ⊤ ⊤ h0 le_rfl)
  congr 1
  exact (Scheme.Hom.appLE_eq_app _).symm

theorem topIso_inv_restrict_appTop {X Y : Scheme.{0}} (π : X ⟶ Y) (U : Y.Opens) :
    U.topIso.inv ≫ (π ∣_ U).appTop = π.app U ≫ (π ⁻¹ᵁ U).topIso.inv := by
  have h0 : (⊤ : (π ⁻¹ᵁ U).toScheme.Opens) ≤ (π ⁻¹ᵁ U).ι ⁻¹ᵁ (π ⁻¹ᵁ U) := fun x _ => x.2
  have h1 : ∀ g : (π ⁻¹ᵁ U).toScheme ⟶ Y, g = (π ⁻¹ᵁ U).ι ≫ π → ∀ h : ⊤ ≤ g ⁻¹ᵁ U,
      g.appLE U ⊤ h = π.app U ≫ (π ⁻¹ᵁ U).topIso.inv := by
    rintro _ rfl h
    rw [topIso_inv_eq_appLE _ h0, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  rw [topIso_inv_appTop U (π ∣_ U) (fun x _ => ((π ∣_ U) x).2)]
  exact h1 _ (morphismRestrict_ι π U) _

theorem evU_val_restrict {X Z : Scheme.{0}} (W : X.Opens) (y : Z ⟶ W.toScheme)
    (h : ∀ z, (y ≫ W.ι) z ∈ W) (r : Γ(X, W)ˣ) :
    (evU (y ≫ W.ι) h r).val = y.appTop.hom (W.topIso.inv.hom r.val) := by
  have e := congrArg (fun φ => φ.hom r.val) (topIso_inv_appTop W y (fun z _ => h z))
  exact e.symm

theorem appTop_injective_of_epi {X Y : Scheme.{0}} (Q : X ⟶ Y) [Epi Q] :
    Function.Injective Q.appTop.hom := by
  intro a b hab
  have e : Q ≫ Out.TLinPf.mOf a = Q ≫ Out.TLinPf.mOf b := by
    rw [Out.TLinPf.comp_mOf, Out.TLinPf.comp_mOf, hab]
  rw [cancel_epi] at e
  rw [← Out.TLinPf.fnOf_mOf a, e, Out.TLinPf.fnOf_mOf]

theorem unit_descends : ∀ {X Y : Scheme.{0}} (π : X ⟶ Y) [Flat π] [Surjective π] [IsAffineHom π] (U : Y.Opens) (r : Γ(X, π ⁻¹ᵁ U)ˣ),
    (∀ (Z : Scheme.{0}) (g₁ g₂ : Z ⟶ X) (h₁ : ∀ z, g₁ z ∈ π ⁻¹ᵁ U) (h₂ : ∀ z, g₂ z ∈ π ⁻¹ᵁ U),
      g₁ ≫ π = g₂ ≫ π → evU g₁ h₁ r = evU g₂ h₂ r) →
    ∃ u : Γ(Y, U)ˣ, pullU π U u = r := by
  intro X Y π _ _ _ U r hr
  have hS : Surjective (π ∣_ U) :=
    MorphismProperty.of_isPullback (P := @Surjective) (isPullback_morphismRestrict π U).flip inferInstance
  have hA : IsAffineHom (π ∣_ U) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) (isPullback_morphismRestrict π U).flip inferInstance
  have hE : Epi (π ∣_ U) := Flat.epi_of_flat_of_surjective _
  have key : ∀ {Z : Scheme.{0}} (y₁ y₂ : Z ⟶ (π ⁻¹ᵁ U).toScheme), y₁ ≫ π ∣_ U = y₂ ≫ π ∣_ U →
      evU (y₁ ≫ (π ⁻¹ᵁ U).ι) (fun z => (y₁ z).2) r = evU (y₂ ≫ (π ⁻¹ᵁ U).ι) (fun z => (y₂ z).2) r := by
    intro Z y₁ y₂ e
    refine hr Z _ _ _ _ ?_
    rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, ← Category.assoc, e, Category.assoc]
  obtain ⟨v, hv⟩ := Out.TLinPf.descend_gen (π ∣_ U) ((π ⁻¹ᵁ U).topIso.inv.hom r.val) (by
    intro Z y₁ y₂ e
    rw [← evU_val_restrict _ y₁ (fun z => (y₁ z).2), ← evU_val_restrict _ y₂ (fun z => (y₂ z).2),
      key y₁ y₂ e])
  obtain ⟨v', hv'⟩ := Out.TLinPf.descend_gen (π ∣_ U) ((π ⁻¹ᵁ U).topIso.inv.hom (r⁻¹).val) (by
    intro Z y₁ y₂ e
    rw [← evU_val_restrict _ y₁ (fun z => (y₁ z).2), ← evU_val_restrict _ y₂ (fun z => (y₂ z).2)]
    have k := key y₁ y₂ e
    simp only [evU, map_inv] at k ⊢
    rw [k])
  have hvv : v * v' = 1 := by
    apply appTop_injective_of_epi (π ∣_ U)
    rw [map_mul, hv, hv', ← map_mul, Units.mul_inv, map_one, map_one]
  have h1 : U.topIso.hom.hom v * U.topIso.hom.hom v' = 1 := by
    rw [← map_mul, hvv, map_one]
  refine ⟨⟨U.topIso.hom.hom v, U.topIso.hom.hom v', h1, by rw [mul_comm, h1]⟩, Units.ext ?_⟩
  change (π.app U).hom (U.topIso.hom.hom v) = r.val
  have e := congrArg (fun φ => φ.hom (U.topIso.hom.hom v)) (topIso_inv_restrict_appTop π U)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  rw [Iso.hom_inv_id_apply, hv] at e
  exact ((π ⁻¹ᵁ U).topIso.symm.commRingCatIsoToRingEquiv.injective e).symm

end GlobalTheory.EigenDescent
