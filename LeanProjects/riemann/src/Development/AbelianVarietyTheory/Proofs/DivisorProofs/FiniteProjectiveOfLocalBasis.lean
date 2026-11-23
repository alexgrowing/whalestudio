import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnivChartOfStandardSmooth
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushRProdPtsResP

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieProj

theorem finite_projective_of_localBasis : ∀ {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (n : ℕ),
    (∀ p : PrimeSpectrum R, ∃ r ∉ p.asIdeal,
      Nonempty (Module.Basis (Fin n) (Localization.Away r) (LocalizedModule (Submonoid.powers r) M))) →
    Module.Finite R M ∧ Module.Projective R M ∧ ∀ p, Module.rankAtStalk (R := R) M p = n := by
  intro R M _ _ _ n h
  let t : Set R := {r | Nonempty (Module.Basis (Fin n) (Localization.Away r)
    (LocalizedModule (Submonoid.powers r) M))}
  have ht : Ideal.span t = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨r, hr, hb⟩ := h ⟨m, hm.isPrime⟩
    exact hr (hle (Ideal.subset_span hb))
  have hfree : ∀ g : t, Module.Free (Localization.Away g.1) (LocalizedModule (Submonoid.powers g.1) M) :=
    fun g => Module.Free.of_basis g.2.some
  have hfp : ∀ g : t, Module.FinitePresentation (Localization.Away g.1)
      (LocalizedModule (Submonoid.powers g.1) M) := fun g => by
    haveI := hfree g
    haveI : Module.Finite (Localization.Away g.1) (LocalizedModule (Submonoid.powers g.1) M) :=
      Module.Finite.of_basis g.2.some
    exact Module.finitePresentation_of_projective _ _
  haveI : Module.FinitePresentation R M := Module.FinitePresentation.of_localizationSpan t ht hfp
  haveI : Module.Flat R M := by
    refine Module.flat_of_localized_span R M t ht ?_
    intro g
    haveI := hfree g
    haveI : Module.Flat R (Localization.Away g.1) := IsLocalization.flat _ (Submonoid.powers g.1)
    exact Module.Flat.trans R (Localization.Away g.1) _
  refine ⟨inferInstance, Module.Flat.projective_of_finitePresentation, fun p => ?_⟩
  obtain ⟨r, hr, ⟨b⟩⟩ := h p
  have hq : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away r))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
    exact hr
  obtain ⟨q, rfl⟩ := hq
  haveI := Module.Free.of_basis b
  haveI : Nontrivial (Localization.Away r) := q.nontrivial
  rw [← Module.rankAtStalk_isBaseChange
    (LocalizedModule.isBaseChange (Submonoid.powers r) M) q,
    Module.rankAtStalk_eq_finrank_of_free]
  change Module.finrank (Localization.Away r) (LocalizedModule (Submonoid.powers r) M) = n
  rw [Module.finrank_eq_card_basis b, Fintype.card_fin]

theorem exists_chart_lieBasis : ∀ {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (n : ℕ),
    SmoothOfRelativeDimension n G.hom → ∀ p : PrimeSpectrum R, ∃ r ∉ p.asIdeal,
      Nonempty (ReciprocityTheory.ChartRestriction.G.Chart.Chart (ReciprocityTheory.ChartRestriction.G.Chart.Gs G r)) ∧
      ∃ v : Fin n → (epsR (Localization.Away r) ⟶ ReciprocityTheory.ChartRestriction.G.Chart.Gs G r), IsLieBasis v := by
  intro R _ G _ _ n h p
  let e : Spec (CommRingCat.of R) ⟶ G.left := η[G].left
  obtain ⟨S, _, _, j, hS, hj, hmem⟩ := GlobalTheory.LieLoc.exists_standardSmooth_chart G n h (e p)
  obtain ⟨_, ⟨r, rfl⟩, hr, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (a := p) (u := (e ⁻¹ᵁ j.left.opensRange).1) hmem (e ⁻¹ᵁ j.left.opensRange).2
  refine ⟨r, hr, ReciprocityTheory.ChartRestriction.G.Chart.chart_away G j.left.opensRange (by haveI : IsAffine (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) S).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of S))); exact isAffineOpen_opensRange j.left) r
    (fun x hx => hsub (show x ∈ (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) from hx)), ?_⟩
  obtain ⟨ε, hε⟩ := GlobalTheory.SqZero.exists_chart_pt j
    (1 : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) (Localization.Away r) ⟶ G) (by
    rintro _ ⟨t, rfl⟩
    have : PrimeSpectrum.comap (algebraMap R (Localization.Away r)) t ∈
        (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
      exact ⟨t, rfl⟩
    exact hsub this)
  obtain ⟨x, hx⟩ := GlobalTheory.LieLoc.univChart_baseChange G n S j _ ε hε.symm
  exact ⟨_, ReciprocityTheory.ChartRestriction.G.Chart.basis_of_chart hx⟩

end GlobalTheory.LieProj
