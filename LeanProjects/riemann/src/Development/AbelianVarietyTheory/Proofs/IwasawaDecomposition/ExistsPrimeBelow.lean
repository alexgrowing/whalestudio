import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NontrivialReferenceForms
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NuInRange
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemLevelOfLocalDepth

open NumberField IsDedekindDomain

namespace GlobalTheory.PrimeBelow

theorem exists_prime_below {K L : Type} [Field K] [Field L] [NumberField K] [NumberField L] (σ : K →+* ℂ) (τ : L →+* ℂ)
    (h : Set.range σ ⊆ Set.range τ) (P : HeightOneSpectrum (𝓞 L)) :
    ∃ p : HeightOneSpectrum (𝓞 K), ∀ (x : 𝓞 K) (y : 𝓞 L), σ (x : K) = τ (y : L) → (x ∈ p.asIdeal ↔ y ∈ P.asIdeal) := by
  classical

  have hmem : ∀ x : K, σ x ∈ τ.range := fun x => RingHom.mem_range.2 (h ⟨x, rfl⟩)
  obtain ⟨ι, hι⟩ : ∃ ι : K →+* L, ∀ x, τ (ι x) = σ x := by
    let e := RingEquiv.ofBijective τ.rangeRestrict
      ⟨fun a b hab => τ.injective (congrArg Subtype.val hab), τ.rangeRestrict_surjective⟩
    refine ⟨e.symm.toRingHom.comp (σ.codRestrict τ.range hmem), fun x => ?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply ⟨σ x, hmem x⟩)
  let φ : 𝓞 K →+* 𝓞 L := RingOfIntegers.mapRingHom ι

  have hne : P.asIdeal.comap φ ≠ ⊥ := by
    have hZ : P.asIdeal.comap (algebraMap ℤ (𝓞 L)) ≠ ⊥ :=
      fun hb => P.ne_bot (Ideal.eq_bot_of_comap_eq_bot hb)
    obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hZ
    intro hbot
    have hmK : ((m : 𝓞 K)) ∈ P.asIdeal.comap φ := by
      rw [Ideal.mem_comap, map_intCast]
      simpa using hm
    rw [hbot, Ideal.mem_bot] at hmK
    have : ((m : K)) = 0 := by
      have := congrArg (fun z : 𝓞 K => (z : K)) hmK
      simpa using this
    exact hm0 (by exact_mod_cast this)
  have := P.isPrime
  refine ⟨⟨P.asIdeal.comap φ, Ideal.comap_isPrime φ P.asIdeal, hne⟩, fun x y hxy => ?_⟩
  have hxy' : φ x = y := by
    apply RingOfIntegers.ext
    apply τ.injective
    rw [RingOfIntegers.mapRingHom_apply, hι, hxy]
  show x ∈ P.asIdeal.comap φ ↔ y ∈ P.asIdeal
  rw [Ideal.mem_comap, hxy']

theorem exists_below : ∀ (D D' : Formalism.BasicNotions.D7), Set.range (⇑(Formalism.BasicNotions.Rows.Data.embLL (Formalism.BasicNotions.D7.what₂ D)) : Formalism.BasicNotions.Rows.Data.LL (Formalism.BasicNotions.D7.what₂ D) → ℂ) ⊆ Set.range (⇑(Formalism.BasicNotions.Rows.Data.embLL (Formalism.BasicNotions.D7.what₂ D')) : Formalism.BasicNotions.Rows.Data.LL (Formalism.BasicNotions.D7.what₂ D') → ℂ) → ∀ (v' : Formalism.BasicNotions.Rows.Places.Pl (Formalism.BasicNotions.Rows.Data.places (Formalism.BasicNotions.D7.what₂ D'))), ∃ (v : Formalism.BasicNotions.Rows.Places.Pl (Formalism.BasicNotions.Rows.Data.places (Formalism.BasicNotions.D7.what₂ D))), GlobalTheory.Mem.Top.Bl.Below D D' v v' := by
  intro D D' h v'
  obtain ⟨p, hp⟩ := exists_prime_below _ _ h (D'.plEq v')
  refine ⟨D.plEq.symm p, fun x x' hx => ?_⟩
  rw [Equiv.apply_symm_apply]
  exact hp x x' hx

end GlobalTheory.PrimeBelow
