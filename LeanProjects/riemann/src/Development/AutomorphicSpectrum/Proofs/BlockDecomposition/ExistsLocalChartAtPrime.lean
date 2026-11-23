import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.CotChart

theorem exists_smooth_chart :
  ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (e : Sp R ⟶ X) (g : ℕ), e ≫ s = 𝟙 _ → SmoothOfRelativeDimension g s → ∀ p : PrimeSpectrum R, ∃ (r : R) (A C : Type) (_ : CommRing A) (_ : CommRing C) (_ : Algebra C A) (_ : Algebra A (Localization.Away r)) (j : Sp A ⟶ X) (k : Sp C ⟶ Sp R), r ∉ p.asIdeal ∧ IsOpenImmersion j ∧ Mono k ∧ j ≫ s = spMap (algebraMap C A) ≫ k ∧ spMap (algebraMap A (Localization.Away r)) ≫ j = spMap (algebraMap R (Localization.Away r)) ≫ e ∧ Module.Free A (KaehlerDifferential C A) ∧ Module.Finite A (KaehlerDifferential C A) ∧ Module.finrank A (KaehlerDifferential C A) = g := by
  intro R _ X s e g _hes hsm p
  obtain ⟨U, hU, V, hV, hxV, hVU, hstd⟩ :=
    hsm.exists_isStandardSmoothOfRelativeDimension (e (show Sp R from p))
  have hopen : IsOpen (((e ⁻¹ᵁ V : (Sp R).Opens) : Set (Sp R)) : Set (PrimeSpectrum R)) :=
    (e ⁻¹ᵁ V).isOpen
  obtain ⟨_, ⟨r, rfl⟩, hpr, hrV⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (a := p) (show p ∈ (((e ⁻¹ᵁ V : (Sp R).Opens) : Set (Sp R)) : Set (PrimeSpectrum R)) from hxV) hopen
  have hr : r ∉ p.asIdeal := hpr
  have hrange0 : Set.range (spMap (algebraMap R (Localization.Away r))) =
      ((PrimeSpectrum.basicOpen r : TopologicalSpace.Opens (PrimeSpectrum R)) : Set (PrimeSpectrum R)) :=
    PrimeSpectrum.localization_away_comap_range (Localization.Away r) r
  have hnt : Nontrivial (Localization.Away r) := by
    have hp : p ∈ Set.range (spMap (algebraMap R (Localization.Away r))) := by
      rw [hrange0]; exact hpr
    obtain ⟨q, -⟩ := hp
    exact (PrimeSpectrum.nonempty_iff_nontrivial).1 ⟨q⟩
  have hrange : Set.range (spMap (algebraMap R (Localization.Away r)) ≫ e) ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    rintro _ ⟨y, rfl⟩
    have hy : (spMap (algebraMap R (Localization.Away r))) y ∈
        ((PrimeSpectrum.basicOpen r : TopologicalSpace.Opens (PrimeSpectrum R)) : Set (PrimeSpectrum R)) := by
      rw [← hrange0]; exact ⟨y, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact hrV hy
  let l : Sp (Localization.Away r) ⟶ Spec Γ(X, V) :=
    IsOpenImmersion.lift hV.fromSpec (spMap (algebraMap R (Localization.Away r)) ≫ e) hrange
  have hl : l ≫ hV.fromSpec = spMap (algebraMap R (Localization.Away r)) ≫ e :=
    IsOpenImmersion.lift_fac _ _ hrange
  let ε : Γ(X, V) ⟶ CommRingCat.of (Localization.Away r) := Spec.preimage l
  have hε : Spec.map ε = l := Spec.map_preimage l
  let φ : Γ(Sp R, U) ⟶ Γ(X, V) := s.appLE U V hVU
  letI aCA : Algebra Γ(Sp R, U) Γ(X, V) := φ.hom.toAlgebra
  letI aAL : Algebra Γ(X, V) (Localization.Away r) := ε.hom.toAlgebra
  have hA : Nontrivial Γ(X, V) := ε.hom.domain_nontrivial
  have hS : Algebra.IsStandardSmoothOfRelativeDimension g Γ(Sp R, U) Γ(X, V) := hstd
  have hS' : Algebra.IsStandardSmooth Γ(Sp R, U) Γ(X, V) := hS.isStandardSmooth
  refine ⟨r, Γ(X, V), Γ(Sp R, U), inferInstance, inferInstance, aCA, aAL, hV.fromSpec, hU.fromSpec,
    hr, inferInstance, inferInstance, ?_, ?_, inferInstance, inferInstance, ?_⟩
  · exact (IsAffineOpen.SpecMap_appLE_fromSpec s hU hV hVU).symm
  · rw [← hl, ← hε]; rfl
  · exact Module.finrank_eq_of_rank_eq
      (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential g)

end GlobalTheory.CompanionTheory.CotChart
