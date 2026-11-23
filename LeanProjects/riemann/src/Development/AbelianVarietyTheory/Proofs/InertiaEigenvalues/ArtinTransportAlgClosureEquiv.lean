import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocUnitApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusRestrictScalarsPowModInertia
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

noncomputable section

namespace GlobalTheory.ArtinTransport

open scoped Pointwise

section Transport

variable {E Ω E' Ω' : Type} [Field E] [Field Ω] [Algebra E Ω] [Field E'] [Field Ω'] [Algebra E' Ω']

theorem valuation_le_one_comap (A' : ValuationSubring Ω') (φ : Ω ≃+* Ω') (y : Ω) :
    (A'.comap φ.toRingHom).valuation y ≤ 1 ↔ A'.valuation (φ y) ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.valuation_le_one_iff]
  exact ValuationSubring.mem_comap

theorem valuation_lt_one_comap (A' : ValuationSubring Ω') (φ : Ω ≃+* Ω') (y : Ω) :
    (A'.comap φ.toRingHom).valuation y < 1 ↔ A'.valuation (φ y) < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', ValuationSubring.mem_comap, ValuationSubring.mem_comap,
    map_eq_zero_iff _ φ.injective]
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, map_inv₀]

variable [NumberField E] [NumberField E'] (A' : ValuationSubring Ω') (φ : Ω ≃+* Ω') {σ : G E Ω} {τ : G E' Ω'}

theorem mem_Dec_comap (h : ∀ z, φ (σ z) = τ (φ z)) (hτ : τ ∈ Dec (F := E') A') :
    σ ∈ Dec (F := E) (A'.comap φ.toRingHom) := by
  have hx : ∀ x, σ x ∈ A'.comap φ.toRingHom ↔ x ∈ A'.comap φ.toRingHom := by
    intro x
    rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap]
    show φ (σ x) ∈ A' ↔ φ x ∈ A'
    rw [h]
    exact apply_mem_iff_of_mem_Dec hτ (φ x)
  show σ • A'.comap φ.toRingHom = A'.comap φ.toRingHom
  ext y
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← hx, mul_inv_apply]

theorem isFrob_comap (h : ∀ z, φ (σ z) = τ (φ z)) {q : ℕ} (hτ : IsFrob (F := E') A' q τ) :
    IsFrob (F := E) (A'.comap φ.toRingHom) q σ := by
  refine ⟨mem_Dec_comap A' φ h hτ.1, fun x hx => ?_⟩
  rw [valuation_lt_one_comap, map_sub, map_pow, h]
  exact hτ.2 _ ((valuation_le_one_comap A' φ x).mp hx)

theorem mem_Ine_comap (h : ∀ z, φ (σ z) = τ (φ z)) (hτ : τ ∈ Ine (F := E') A') :
    σ ∈ Ine (F := E) (A'.comap φ.toRingHom) := by
  refine ⟨mem_Dec_comap A' φ h hτ.1, fun x hx => ?_⟩
  rw [valuation_lt_one_comap, map_sub, h]
  exact hτ.2 _ ((valuation_le_one_comap A' φ x).mp hx)

end Transport

variable {E Ω E' Ω' : Type} [Field E] [Field Ω] [Algebra E Ω] [Field E'] [Field Ω'] [Algebra E' Ω'] [Algebra E E']

theorem exists_conj (φ : Ω ≃+* Ω') (hφ : ∀ x, φ (algebraMap E Ω x) = algebraMap E' Ω' (algebraMap E E' x))
    (τ : G E' Ω') : ∃ σ : G E Ω, ∀ z, φ (σ z) = τ (φ z) := by
  refine ⟨AlgEquiv.ofRingEquiv (f := (φ.trans τ.toRingEquiv).trans φ.symm) fun x => ?_, fun z => ?_⟩
  · show φ.symm (τ (φ (algebraMap E Ω x))) = algebraMap E Ω x
    rw [hφ, AlgEquiv.commutes, ← hφ, φ.symm_apply_apply]
  · show φ (φ.symm (τ (φ z))) = τ (φ z)
    exact φ.apply_symm_apply _

theorem isPlaceOver_comap [NumberField E] [NumberField E'] (φ : Ω ≃+* Ω')
    (hφ : ∀ x, φ (algebraMap E Ω x) = algebraMap E' Ω' (algebraMap E E' x))
    {v : HeightOneSpectrum (𝓞 E)} {w : HeightOneSpectrum (𝓞 E')}
    (hwv : w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 E')) = v.asIdeal) {A' : ValuationSubring Ω'}
    (hA : IsPlaceOver A' w) : IsPlaceOver (A'.comap φ.toRingHom) v := by
  intro x
  rw [valuation_lt_one_comap, hφ, ← hwv, Ideal.mem_comap, ← hA (algebraMap (𝓞 E) (𝓞 E') x)]
  rfl

theorem normV_eq_pow [NumberField E] [NumberField E'] {v : HeightOneSpectrum (𝓞 E)} {w : HeightOneSpectrum (𝓞 E')}
    (hwv : w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 E')) = v.asIdeal) :
    normV w = normV v ^ w.asIdeal.inertiaDeg (𝓞 E) := by
  have : w.asIdeal.LiesOver v.asIdeal := ⟨hwv.symm⟩
  simp only [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  exact (Ideal.absNorm_pow_inertiaDeg v.asIdeal w.asIdeal).symm

end GlobalTheory.ArtinTransport

namespace GlobalTheory.ArtinTransport

theorem chi_artin_transport : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] [Algebra E E'] (φ : Ω ≃+* Ω'), (∀ x, φ (algebraMap E Ω x) = algebraMap E' Ω' (algebraMap E E' x)) → ∀ (art : Neutral.B1.Ideles E →* GlobalTheory.HeckeGal.Gab E Ω) (art' : Neutral.B1.Ideles E' →* GlobalTheory.HeckeGal.Gab E' Ω'), GlobalTheory.HeckeGal.IsGlobalArtin art → GlobalTheory.HeckeGal.IsGlobalArtin art' → ∀ (ρ : GlobalTheory.HeckeGal.Gab E' Ω' →* GlobalTheory.HeckeGal.Gab E Ω), (∀ (τ : Formalism.ConjugateSelfDual.G E' Ω') (σ : Formalism.ConjugateSelfDual.G E Ω), (∀ z, φ (σ z) = τ (φ z)) → ρ (GlobalTheory.HeckeGal.toAb E' Ω' τ) = GlobalTheory.HeckeGal.toAb E Ω σ) → ∀ (B : Type) [CommGroup B] (χ : GlobalTheory.HeckeGal.Gab E Ω →* B) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E')), w.asIdeal.comap (algebraMap (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers E')) = v.asIdeal → (∀ x, Formalism.L2.Host.IsUnitAt v x → χ (art (Neutral.B1.localIdele E v x)) = 1) → (∀ x, Formalism.L2.Host.IsUnitAt w x → χ (ρ (art' (Neutral.B1.localIdele E' w x))) = 1) ∧ ∀ x ϖ, Formalism.L2.Host.IsUnifAt w x → Formalism.L2.Host.IsUnifAt v ϖ → χ (ρ (art' (Neutral.B1.localIdele E' w x))) = χ (art (Neutral.B1.localIdele E v ϖ)) ^ w.asIdeal.inertiaDeg (NumberField.RingOfIntegers E) := by
  intro E Ω _ _ _ _ _ E' Ω' _ _ _ _ _ _ φ hφ art art' ha ha' ρ hρ B _ χ v w hwv hχ
  obtain ⟨A', hA'⟩ := exists_isPlaceOver (F := E') Ω' w
  have hA : IsPlaceOver (A'.comap φ.toRingHom) v := isPlaceOver_comap φ hφ hwv hA'

  have hI : ∀ ι ∈ Ine (F := E) (A'.comap φ.toRingHom), χ (toAb E Ω ι) = 1 := by
    intro ι hι
    obtain ⟨u, hu, e⟩ := (ha.ine v _ hA (toAb E Ω ι)).mpr ⟨ι, hι, rfl⟩
    rw [← e]
    exact hχ u hu
  refine ⟨fun x hx => ?_, fun x ϖ hx hϖ => ?_⟩
  · obtain ⟨τ, hτ, e⟩ := (ha'.ine w A' hA' _).mp ⟨x, hx, rfl⟩
    obtain ⟨σ, hσ⟩ := exists_conj φ hφ τ
    rw [← e, hρ τ σ hσ]
    exact hI σ (mem_Ine_comap A' φ hσ hτ)
  · obtain ⟨τ, hτ, e⟩ := (ha'.frob w A' hA' _).mp ⟨x, hx, rfl⟩
    obtain ⟨σ₀, hσ₀, e₀⟩ := (ha.frob v _ hA _).mp ⟨ϖ, hϖ, rfl⟩
    obtain ⟨σ, hσ⟩ := exists_conj φ hφ τ
    have hσi : ∀ z, φ (σ⁻¹ z) = τ⁻¹ (φ z) := by
      intro z
      have h1 : τ (τ⁻¹ (φ z)) = τ (φ (σ⁻¹ z)) := by
        rw [mul_inv_apply, ← hσ, mul_inv_apply]
      exact (τ.injective h1).symm
    set f := w.asIdeal.inertiaDeg (𝓞 E)
    have hF : IsFrob (F := E) (A'.comap φ.toRingHom) (normV v ^ f) σ := by
      rw [← normV_eq_pow hwv]
      exact isFrob_comap A' φ hσ hτ
    have hm := hI _ (inv_mul_mem_Ine_of_isFrob (GlobalTheory.FrobRestrict.isFrob_pow hσ₀ f) hF)
    rw [← e, hρ _ _ hσi, ← e₀, map_inv, map_inv, map_inv, map_inv, inv_pow, inv_inj]
    rw [map_mul, map_mul, map_inv, map_inv, map_pow, map_pow] at hm
    exact (inv_mul_eq_one.mp hm).symm

end GlobalTheory.ArtinTransport
