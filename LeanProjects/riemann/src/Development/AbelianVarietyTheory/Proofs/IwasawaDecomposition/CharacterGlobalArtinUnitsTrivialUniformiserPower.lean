import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocUnitApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusRestrictScalarsPowModInertiaStatement
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

namespace GlobalTheory.NormCompat

theorem chi_artin_restrict : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (K : IntermediateField E Ω) [FiniteDimensional E K] [NumberField K] [IsAlgClosure K Ω] (art : Ideles E →* Gab E Ω) (artK : Ideles K →* Gab K Ω), IsGlobalArtin art → IsGlobalArtin artK → ∀ (ρ : Gab K Ω →* Gab E Ω), (∀ τ : G K Ω, ρ (toAb K Ω τ) = toAb E Ω (τ.restrictScalars E)) → ∀ (B : Type) [CommGroup B] (χ : Gab E Ω →* B) (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 K)), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → (∀ x, IsUnitAt v x → χ (art (localIdele E v x)) = 1) → (∀ x, IsUnitAt w x → χ (ρ (artK (localIdele K w x))) = 1) ∧ ∀ x ϖ, IsUnifAt w x → IsUnifAt v ϖ → χ (ρ (artK (localIdele K w x))) = χ (art (localIdele E v ϖ)) ^ w.asIdeal.inertiaDeg (𝓞 E) := by
  intro E Ω _ _ _ _ _ K _ _ _ art artK ha haK ρ hρ B _ χ v w hwv hχ
  obtain ⟨A, hAw⟩ := exists_isPlaceOver (F := K) Ω w
  obtain ⟨hAv, -, hine, hfrob⟩ := GlobalTheory.T.frobenius_restrictScalars_pow_mod_inertia E Ω K v w hwv A hAw

  have hI : ∀ ι ∈ Ine (F := E) A, χ (toAb E Ω ι) = 1 := by
    intro ι hι
    obtain ⟨u, hu, e⟩ := (ha.ine v A hAv (toAb E Ω ι)).mpr ⟨ι, hι, rfl⟩
    rw [← e]
    exact hχ u hu
  refine ⟨fun x hx => ?_, fun x ϖ hx hϖ => ?_⟩
  · obtain ⟨ι, hι, e⟩ := (haK.ine w A hAw _).mp ⟨x, hx, rfl⟩
    rw [← e, hρ]
    exact hI _ (hine ι hι)
  · obtain ⟨σ, hσ, e⟩ := (haK.frob w A hAw _).mp ⟨x, hx, rfl⟩
    obtain ⟨φ, hφ, e'⟩ := (ha.frob v A hAv _).mp ⟨ϖ, hϖ, rfl⟩
    have hm := hI _ (hfrob σ φ hσ hφ)
    have hr : (σ⁻¹).restrictScalars E = (σ.restrictScalars E)⁻¹ := AlgEquiv.ext fun _ => rfl
    rw [← e, hρ, ← e', hr, map_inv, map_inv, map_inv, map_inv, inv_pow]
    rw [map_mul, map_mul, map_inv, map_inv, map_pow, map_pow] at hm
    rw [inv_inj]
    exact mul_inv_eq_one.mp hm

end GlobalTheory.NormCompat
