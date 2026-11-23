import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianDeRhamStructure
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineH2SmallCoverBijective

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.TrivSmall

variable {R : Type} [CommRing R] {X : Scheme.{0}}

theorem isTriv_loc (s : X ⟶ Sp R) (T : (IsTriv s).FullSubcategory) (b : T.obj.B) :
    IsTriv s (ThickLoc.loc T.obj b) := by
  change Ideal.map _ T.obj.J = ⊥
  rw [show T.obj.J = ⊥ from T.property, Ideal.map_bot]

theorem hasLoc (s : X ⟶ Sp R) : Desc.HasLoc ((IsTriv s).ι ⋙ O (dp0 R) s) := by
  intro T b
  let b' : T.obj.B := b
  refine ⟨⟨ThickLoc.loc T.obj b', isTriv_loc s T b'⟩, ObjectProperty.homMk (ThickLoc.toLoc T.obj b'),
    IsLocalization.Away.algebraMap_isUnit (S := Localization.Away b') b',
    fun y ↦ IsLocalization.Away.surj (S := Localization.Away b') b' y, fun x hx ↦ ?_,
    fun S u hu ↦ ⟨ObjectProperty.homMk (ThickLoc.lift u.hom hu), ?_, fun v hv ↦ ?_⟩⟩
  · obtain ⟨⟨_, n, rfl⟩, hm⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers b') (Localization.Away b') x).1 hx
    exact ⟨n, hm⟩
  · exact ObjectProperty.hom_ext _ (Thick.hom_ext (ThickLoc.liftφ_algebraMap u.hom hu))
  · have hv' : ∀ x : T.obj.B, v.hom.φ (algebraMap T.obj.B (Localization.Away b') x) = u.hom.φ x :=
      fun x ↦ by rw [← hv]; rfl
    have : (v.hom.φ : Localization.Away b' →+* S.obj.B) =
        (ThickLoc.liftφ u.hom hu : Localization.Away b' →+* S.obj.B) := by
      refine IsLocalization.ringHom_ext (Submonoid.powers b') (RingHom.ext fun x ↦ ?_)
      exact (hv' x).trans (ThickLoc.liftφ_algebraMap u.hom hu x).symm
    exact ObjectProperty.hom_ext _ (Thick.hom_ext fun x ↦ RingHom.congr_fun this x)

theorem pull_restrict_small_injective : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (K : Type) (U : K → X.Opens), ⨆ i, U i = ⊤ → Function.Injective (CoefMap.restrict ((IsTriv s).ι ⋙ O (dp0 R) s) (ObjectProperty.ι (fun T : (IsTriv s).FullSubcategory => IsSmall (dp0 R) s U T.obj))).pull2 := by
  intro R _ X s K U hU
  exact (Desc.pull2_bijective _ (hasLoc s) _ (fun _ _ φ h ↦ h.imp fun _ ↦ φ.hom.le_preimage)
    fun T ↦ by
      obtain ⟨n, b, hb, h⟩ := exists_finite_small_cover R ⊥ (dp0 R) X s K U hU T.obj
      exact ⟨n, b, hb, fun i S u hu ↦ h i S.obj u.hom hu⟩).1

end GlobalTheory.CompanionTheory.TrivSmall
