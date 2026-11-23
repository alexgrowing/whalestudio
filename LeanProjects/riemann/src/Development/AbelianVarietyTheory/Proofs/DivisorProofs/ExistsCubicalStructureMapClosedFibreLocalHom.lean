import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEvenPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.UU.ClosedFib

theorem le_comap_max {R W : Type} [CommRing R] [IsLocalRing R] [CommRing W] [IsLocalRing W] (φ : R →+* W)
    (hφ : IsLocalHom φ) : maximalIdeal R ^ (0 + 1) ≤ (maximalIdeal W ^ (0 + 1)).comap φ := by
  simp only [zero_add, pow_one]
  exact fun x hx => (mem_maximalIdeal _).2 fun h => (mem_maximalIdeal _).1 hx (isUnit_of_map_unit φ x h)

theorem spMap_thick {R W : Type} [CommRing R] [IsLocalRing R] [CommRing W] [IsLocalRing W] (φ : R →+* W)
    (hφ : IsLocalHom φ) :
    spMap (Ideal.quotientMap (maximalIdeal W ^ (0 + 1)) φ (le_comap_max φ hφ)) ≫ thick R (maximalIdeal R) 0 =
      thick W (maximalIdeal W) 0 ≫ spMap φ := by
  simp only [spMap, thick, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.quotientMap_comp_mk]

theorem exists_isCPMap_closedFibre : ∀ (R W : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing W] [IsDomain W] [IsLocalRing W] (φ : R →+* W), IsLocalHom φ → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (β : G'.left ⟶ G.left) (hβ : IsGrpPullback G' G (spMap φ) β) (P : GlobalTheory.UU.CP G) (P' : GlobalTheory.UU.CP G') (w : LB.Iso P'.L.L (P.L.L.pull β)), GlobalTheory.UU.IsCPMap P' P (spMap φ) β hβ.1.w w → ∀ (P₀ : GlobalTheory.UU.CP (thickObj R (maximalIdeal R) 0 G)) (P'₀ : GlobalTheory.UU.CP (thickObj W (maximalIdeal W) 0 G')), GlobalTheory.UU.IsLevelCP (maximalIdeal R) 0 P₀ P → GlobalTheory.UU.IsLevelCP (maximalIdeal W) 0 P'₀ P' → ∃ (ρ : R ⧸ maximalIdeal R ^ (0 + 1) →+* W ⧸ maximalIdeal W ^ (0 + 1)) (β₀ : (thickObj W (maximalIdeal W) 0 G').left ⟶ (thickObj R (maximalIdeal R) 0 G).left) (hβ₀ : IsGrpPullback (thickObj W (maximalIdeal W) 0 G') (thickObj R (maximalIdeal R) 0 G) (spMap ρ) β₀) (w₀ : LB.Iso P'₀.L.L (P₀.L.L.pull β₀)), GlobalTheory.UU.IsCPMap P'₀ P₀ (spMap ρ) β₀ hβ₀.1.w w₀ := by
  intro R W _ _ _ _ _ _ φ hφ G _ _ G' _ _ β hβ P P' w hP P₀ P'₀ h₀ h₀'
  let ρ := Ideal.quotientMap (maximalIdeal W ^ (0 + 1)) φ (le_comap_max φ hφ)
  have sq : spMap ρ ≫ thick R (maximalIdeal R) 0 = thick W (maximalIdeal W) 0 ≫ spMap φ := spMap_thick φ hφ
  let β₀ : (thickObj W (maximalIdeal W) 0 G').left ⟶ (thickObj R (maximalIdeal R) 0 G).left :=
    pullback.lift (pullback.fst G'.hom (thick W (maximalIdeal W) 0) ≫ β)
      (pullback.snd G'.hom (thick W (maximalIdeal W) 0) ≫ spMap ρ) (by
        rw [Category.assoc, hβ.1.w, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc, sq])
  have e₁ : β₀ ≫ pullback.fst G.hom (thick R (maximalIdeal R) 0) =
      pullback.fst G'.hom (thick W (maximalIdeal W) 0) ≫ β := pullback.lift_fst _ _ _
  have e₂ : β₀ ≫ (thickObj R (maximalIdeal R) 0 G).hom = (thickObj W (maximalIdeal W) 0 G').hom ≫ spMap ρ :=
    pullback.lift_snd _ _ _
  have n : IsGrpPullback (thickObj W (maximalIdeal W) 0 G') G (spMap ρ ≫ thick R (maximalIdeal R) 0)
      (β₀ ≫ pullback.fst G.hom (thick R (maximalIdeal R) 0)) :=
    (IsGrpPullback.comp (isGrpPullback_pullback G' (thick W (maximalIdeal W) 0)) hβ).congr sq.symm e₁.symm
  have hβ₀ : IsGrpPullback (thickObj W (maximalIdeal W) 0 G') (thickObj R (maximalIdeal R) 0 G) (spMap ρ) β₀ :=
    (isGrpPullback_pullback G (thick R (maximalIdeal R) 0)).cancel n e₂
  obtain ⟨_, hR⟩ := h₀
  obtain ⟨_, hW⟩ := h₀'
  obtain ⟨_, -, hc⟩ := hP.exists_comp hW (by
    rw [Category.assoc, hβ.1.w, ← Category.assoc, pullback.condition, Category.assoc]; rfl)
  obtain ⟨w₀, hw₀⟩ := GlobalTheory.UU.TowerEx.exists_cancel hR hc hβ₀ sq e₁
  exact ⟨ρ, β₀, hβ₀, w₀, hw₀⟩

end GlobalTheory.UU.ClosedFib
