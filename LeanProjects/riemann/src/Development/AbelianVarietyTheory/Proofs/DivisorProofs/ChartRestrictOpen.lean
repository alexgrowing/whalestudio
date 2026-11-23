import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitChartAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelOpenNoetherian

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

theorem isTest_comp_opens_ι {p : ℕ} [Fact p.Prime] {X : Scheme.{0}} (U Xw : X.Opens)
    (yb : Sp 𝓞_ℂ_[p] ⟶ U.toScheme) (h : IsTest p (U.ι ⁻¹ᵁ Xw) yb) : IsTest p Xw (yb ≫ U.ι) := by
  obtain ⟨⟨T, kO, yT, hT, hk, he⟩, hr⟩ := h
  refine ⟨⟨T, kO, yT ≫ U.ι, hT, hk, by rw [← Category.assoc, he]⟩, ?_⟩
  rintro _ ⟨w, rfl⟩
  have := hr ⟨w, rfl⟩
  simpa [Scheme.Hom.comp_apply] using this

theorem chartAt_opens_restrict : ∀ (p n : ℕ) [Fact p.Prime] (X : Scheme.{0}) (U Xw : X.Opens) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p])
    (x : U.toScheme), ChartAt p n Xw K (U.ι x) → ChartAt p n (U.ι ⁻¹ᵁ Xw) (fun yb => K (yb ≫ U.ι)) x := by
  intro p n _ X U Xw K x h
  obtain ⟨R, _, ξ, J, _, Q, u, hξ, ⟨z, hz⟩, hT⟩ := h
  have hxU : U.ι x ∈ (U : Set X) := by rw [← Scheme.Opens.range_ι]; exact ⟨x, rfl⟩
  have hzU : z ∈ ((ξ ⁻¹ᵁ U : (Sp R).Opens) : Set (Sp R)) := by
    show ξ z ∈ U
    rw [hz]; exact hxU
  obtain ⟨_, ⟨f, rfl⟩, hzf, hfU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hzU (ξ ⁻¹ᵁ U).isOpen
  let ι' := algebraMap R (Localization.Away f)
  have hrange : Set.range (spMap ι') = (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) :=
    PrimeSpectrum.localization_away_comap_range (Localization.Away f) f
  have hsub : Set.range (spMap ι' ≫ ξ) ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    have hy : (spMap ι') y ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := hrange ▸ ⟨y, rfl⟩
    exact hfU hy
  obtain ⟨ξ₁, hfac⟩ : ∃ ξ₁ : Sp (Localization.Away f) ⟶ U.toScheme, ξ₁ ≫ U.ι = spMap ι' ≫ ξ :=
    ⟨_, IsOpenImmersion.lift_fac _ _ hsub⟩
  have hξ₁ : IsOpenImmersion ξ₁ := by
    haveI : IsOpenImmersion (ξ₁ ≫ U.ι) := by rw [hfac]; infer_instance
    exact IsOpenImmersion.of_comp ξ₁ U.ι
  let Q' : J → Localization.Away f := fun j => ι' (Q j)
  have hunit : ∀ j, IsUnit (((algebraMap (Localization.Away f) (Localization.Away ((p : Localization.Away f) * Q' j))).comp ι')
      ((p : R) * Q j)) := by
    intro j
    rw [RingHom.comp_apply, map_mul, map_natCast]
    exact IsLocalization.Away.algebraMap_isUnit _
  obtain ⟨g, hg⟩ : ∃ g : ∀ j, Localization.Away ((p : R) * Q j) →+* Localization.Away ((p : Localization.Away f) * Q' j),
      ∀ j, (g j).comp (algebraMap R _) = (algebraMap (Localization.Away f) _).comp ι' :=
    ⟨fun j => IsLocalization.Away.lift ((p : R) * Q j) (hunit j),
      fun j => IsLocalization.Away.lift_comp _ (hunit j)⟩
  refine ⟨Localization.Away f, inferInstance, ξ₁, J, inferInstance, Q', fun j => Units.map (g j : _ →* _) (u j), hξ₁,
    ?_, ?_⟩
  · have hz' : z ∈ Set.range (spMap ι') := hrange ▸ hzf
    obtain ⟨z', rfl⟩ := hz'
    refine ⟨z', (Scheme.Hom.isOpenEmbedding U.ι).injective ?_⟩
    rw [← hz, ← Scheme.Hom.comp_apply, hfac, Scheme.Hom.comp_apply]
  · intro φ' hφ'
    have heq : spMap (φ'.comp ι') ≫ ξ = (spMap φ' ≫ ξ₁) ≫ U.ι := by
      rw [Category.assoc, hfac, sp_sp]
    obtain ⟨⟨j0, hj0⟩, hall⟩ := hT (φ'.comp ι') (by rw [heq]; exact isTest_comp_opens_ι U Xw _ hφ')
    refine ⟨⟨j0, hj0⟩, fun j hj ψ' hψ' κ hκ => ?_⟩
    have := hall j hj (ψ'.comp (g j))
      (by rw [RingHom.comp_assoc, hg j, ← RingHom.comp_assoc, hψ', RingHom.comp_assoc]) κ (by rw [heq]; exact hκ)
    exact this

end GlobalTheory.FlatModel
