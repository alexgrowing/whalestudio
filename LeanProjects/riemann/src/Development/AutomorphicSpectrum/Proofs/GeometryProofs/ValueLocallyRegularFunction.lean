import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SectionNear

theorem germ_closedPoint {Y : Scheme.{0}} {R : CommRingCat.{0}} [IsLocalRing R] (f : Spec R ⟶ Y) (U : Y.Opens)
    (hU : f (IsLocalRing.closedPoint R) ∈ U) (h : ⊤ ≤ f ⁻¹ᵁ U) :
    Y.presheaf.germ U _ hU ≫ Scheme.stalkClosedPointTo f =
      f.appLE U ⊤ h ≫ (Scheme.ΓSpecIso R).hom := by
  rw [Scheme.germ_stalkClosedPointTo]
  simp [Iso.trans_hom, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map_assoc]

theorem fromSpec_appLE_self {T : Scheme.{0}} {V : T.Opens} (hV : IsAffineOpen V) (h : ⊤ ≤ hV.fromSpec ⁻¹ᵁ V) :
    hV.fromSpec.appLE V ⊤ h ≫ (Scheme.ΓSpecIso Γ(T, V)).hom = 𝟙 _ := by
  have e : (Spec Γ(T, V)).presheaf.map (eqToHom hV.fromSpec_preimage_self).op ≫
      (Spec Γ(T, V)).presheaf.map (homOfLE h).op = 𝟙 _ := by
    have e₀ : (eqToHom hV.fromSpec_preimage_self).op ≫ (homOfLE h).op = 𝟙 _ :=
      Quiver.Hom.unop_inj (Subsingleton.elim _ _)
    rw [← Functor.map_comp, e₀, CategoryTheory.Functor.map_id]
  rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, Category.assoc,
    reassoc_of% e]
  simp

theorem spMap_fromSpec_appLE {T : Scheme.{0}} {V : T.Opens} (hV : IsAffineOpen V) (χ : Γ(T, V) →+* ℂ)
    (h : ⊤ ≤ (spMap χ ≫ hV.fromSpec) ⁻¹ᵁ V) :
    (spMap χ ≫ hV.fromSpec).appLE V ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom = CommRingCat.ofHom χ := by
  have h₁ : ⊤ ≤ hV.fromSpec ⁻¹ᵁ V := hV.fromSpec_preimage_self.ge
  have n := Scheme.ΓSpecIso_naturality (R := Γ(T, V)) (S := CommRingCat.of ℂ) (CommRingCat.ofHom χ)
  have a : (spMap χ).appLE ⊤ ⊤ le_top = Scheme.Hom.appTop (spMap χ) := by
    simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
    exact Category.comp_id _
  rw [← Scheme.Hom.appLE_comp_appLE (spMap χ) hV.fromSpec V ⊤ ⊤ h₁ le_top, a, Category.assoc, n,
    reassoc_of% (fromSpec_appLE_self hV h₁)]

theorem section_near : ∀ (X T : Scheme.{0}) (j : T ⟶ X) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), IsCptGen ξ → ∀ (y₀ : Sp ℂ ⟶ T) (t : Ω) (r₀ : ℂ), ValAt ξ (y₀ ≫ j) t r₀ → ∃ W₁ : T.Opens, ⊤ ≤ y₀ ⁻¹ᵁ W₁ ∧ ∀ (V : T.Opens) (hV : IsAffineOpen V), V ≤ W₁ → ∃ g : Γ(T, V), ∀ (χ : Γ(T, V) →+* ℂ) (r : ℂ), ValAt ξ ((spMap χ ≫ hV.fromSpec) ≫ j) t r → r = χ g := by
  intro X T j Ω _ ξ hξ y₀ t r₀ h₀
  obtain ⟨h, s, hs, -⟩ := h₀
  obtain ⟨N, hp, G, rfl⟩ := TopCat.Presheaf.germ_exist X.presheaf s
  have hgen : genPt ξ ∈ N := h.mem_open N.2 hp
  have hgerm : ∀ (p : Cpt ξ) (hp : p.1 ∈ N), genMap ξ p (X.presheaf.germ N p.1 hp G) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ N (genPt ξ) hgen G) := by
    intro p hp
    have e := TopCat.Presheaf.germ_stalkSpecializes X.presheaf hp p.2
    have e' : (X.presheaf.stalkSpecializes p.2).hom (X.presheaf.germ N p.1 hp G) =
        X.presheaf.germ N (genPt ξ) hgen G := by
      rw [← e]; rfl
    exact congrArg (Scheme.stalkClosedPointTo ξ).hom e'
  refine ⟨j ⁻¹ᵁ N, ?_, fun V hV hVN => ⟨j.appLE N V hVN G, fun χ r hr => ?_⟩⟩
  · intro x _
    have hx : x = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    subst hx
    exact hp
  · obtain ⟨h', s', hs', rfl⟩ := hr
    have hcV : (spMap χ ≫ hV.fromSpec) (IsLocalRing.closedPoint ℂ) ∈ V := by
      have : hV.fromSpec ((spMap χ) (IsLocalRing.closedPoint ℂ)) ∈ Set.range hV.fromSpec := ⟨_, rfl⟩
      rw [hV.range_fromSpec] at this
      exact this
    have hq : centre ((spMap χ ≫ hV.fromSpec) ≫ j) ∈ N := hVN hcV
    have e : s' = X.presheaf.germ N _ hq G :=
      hξ.inj ⟨_, h'⟩ (hs'.trans ((hs.symm.trans (hgerm ⟨_, h⟩ hp)).trans (hgerm ⟨_, h'⟩ hq).symm))
    subst e
    have e₂ : ⊤ ≤ (spMap χ ≫ hV.fromSpec) ⁻¹ᵁ V :=
      (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of ℂ) _ hcV).ge
    have k := germ_closedPoint (R := CommRingCat.of ℂ) ((spMap χ ≫ hV.fromSpec) ≫ j) N hq
      (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of ℂ) _ hq).ge
    have d : ((spMap χ ≫ hV.fromSpec) ≫ j).appLE N ⊤
        (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of ℂ) _ hq).ge ≫
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom = j.appLE N V hVN ≫ CommRingCat.ofHom χ := by
      rw [← Scheme.Hom.appLE_comp_appLE (spMap χ ≫ hV.fromSpec) j N V ⊤ hVN e₂, Category.assoc,
        spMap_fromSpec_appLE hV χ e₂]
    exact congrArg (fun φ => φ.hom G) (k.trans d)

end GlobalTheory.CompanionTheory.Ar.SectionNear
