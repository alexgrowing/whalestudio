import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilpotentKerAppStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPushoutOfNilpotentThickeningsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFerrandPushoutOverFibreProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueFlatOverPullbackOfSubsingletonStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

set_option autoImplicit false

namespace GlobalTheory.FerrandGlue

theorem kernel_nilpotent : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₂ → Nontrivial R₀ → IsNilpotent (RingHom.ker g₁.hom) := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hg₂ hR₀
  have hT := (Types.isPullback_iff _ _ _ _).1 (hP.map (forget CommRingCat))
  have hf₁ : Function.Surjective f₁ := by
    intro r
    obtain ⟨s, hs⟩ := hg₂ (g₁ r)
    obtain ⟨p, hp, -⟩ := hT.2.2 r s hs.symm
    exact ⟨p, hp⟩
  let J : Ideal P := (RingHom.ker g₁.hom).comap f₁.hom
  have hJ : J ≤ IsLocalRing.maximalIdeal P := IsLocalRing.le_maximalIdeal (by
    intro h
    have h1 : (1 : P) ∈ J := h ▸ Submodule.mem_top
    simp [J] at h1)
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := P)
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hn
  refine ⟨n, ?_⟩
  have hmap : RingHom.ker g₁.hom = J.map f₁.hom := (Ideal.map_comap_of_surjective _ hf₁ _).symm
  rw [hmap, ← Ideal.map_pow, Ideal.zero_eq_bot, eq_bot_iff]
  calc (J ^ n).map f₁.hom ≤ ((IsLocalRing.maximalIdeal P) ^ n).map f₁.hom := Ideal.map_mono (Ideal.pow_right_mono hJ n)
    _ = ⊥ := by rw [hn, Ideal.zero_eq_bot, Ideal.map_bot]

theorem thickening_of_isPullback : ∀ (R₁ R₀ : CommRingCat.{0}) (g : R₁ ⟶ R₀) (Y₁ Y₀ : Scheme.{0}) (p₁ : Y₁ ⟶ Spec R₁) (p₀ : Y₀ ⟶ Spec R₀) (i : Y₀ ⟶ Y₁), IsPullback i p₀ p₁ (Spec.map g) → Function.Surjective g → IsNilpotent (RingHom.ker g.hom) → IsClosedImmersion i ∧ Surjective i := by
  intro R₁ R₀ g Y₁ Y₀ p₁ p₀ i h hg hn
  have hc : IsClosedImmersion (Spec.map g) := IsClosedImmersion.spec_of_surjective g hg
  have hs : Surjective (Spec.map g) := by
    constructor
    intro x
    obtain ⟨n, hn⟩ := hn
    have hx : x ∈ PrimeSpectrum.zeroLocus (RingHom.ker g.hom : Set R₁) := fun a ha => by
      refine x.isPrime.mem_of_pow_mem n ?_
      have := Ideal.pow_mem_pow ha n
      rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at this
      rw [this]
      exact zero_mem _
    rw [← range_comap_of_surjective _ g.hom hg] at hx
    exact hx
  exact ⟨MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip hc,
    MorphismProperty.of_isPullback (P := @Surjective) h.flip hs⟩

theorem ferrand_glue_artinian : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (Y₁ : Over (Spec R₁)) (Y₂ : Over (Spec R₂)) (Y₀ : Over (Spec R₀)) (i₁ : Y₀.left ⟶ Y₁.left) (i₂ : Y₀.left ⟶ Y₂.left), IsPullback i₁ Y₀.hom Y₁.hom (Spec.map g₁) → IsPullback i₂ Y₀.hom Y₂.hom (Spec.map g₂) → Flat Y₁.hom → Flat Y₂.hom → ∃ (Y : Over (Spec P)) (j₁ : Y₁.left ⟶ Y.left) (j₂ : Y₂.left ⟶ Y.left), IsPullback j₁ Y₁.hom Y.hom (Spec.map f₁) ∧ IsPullback j₂ Y₂.hom Y.hom (Spec.map f₂) ∧ Flat Y.hom ∧ IsPushout i₁ i₂ j₁ j₂ := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hg₁ hg₂ Y₁ Y₂ Y₀ i₁ i₂ h₁ h₂ hf₁ hf₂
  by_cases hR₀ : Subsingleton R₀
  · exact GlobalTheory.T.glue_flat_over_pullback_of_subsingleton P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hR₀ hloc hart hg₁ hg₂ Y₁ Y₂ Y₀ i₁ i₂ h₁ h₂ hf₁ hf₂
  rw [not_subsingleton_iff_nontrivial] at hR₀
  have hn₁ := kernel_nilpotent P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hg₂ hR₀
  have hn₂ := kernel_nilpotent P R₂ R₁ R₀ f₂ f₁ g₂ g₁ hP.flip hloc hart hg₁ hR₀
  obtain ⟨hc₁, hs₁⟩ := thickening_of_isPullback R₁ R₀ g₁ Y₁.left Y₀.left Y₁.hom Y₀.hom i₁ h₁ hg₁ hn₁
  obtain ⟨hc₂, hs₂⟩ := thickening_of_isPullback R₂ R₀ g₂ Y₂.left Y₀.left Y₂.hom Y₀.hom i₂ h₂ hg₂ hn₂
  obtain ⟨Y, j₁, j₂, hw, hpo, hj₁, hj₂, hV⟩ := GlobalTheory.T.exists_pushout_of_nilpotent_thickenings' Y₀.left Y₁.left Y₂.left i₁ i₂ hc₁ hc₂ hs₁ hs₂
    (GlobalTheory.T.isNilpotent_ker_app_of_isPullback_of_nilpotent R₁ R₀ g₁ Y₁.left Y₀.left Y₁.hom Y₀.hom i₁ h₁ hg₁ hn₁)
    (GlobalTheory.T.isNilpotent_ker_app_of_isPullback_of_nilpotent R₂ R₀ g₂ Y₂.left Y₀.left Y₂.hom Y₀.hom i₂ h₂ hg₂ hn₂)
  have hcomm : i₁ ≫ Y₁.hom ≫ Spec.map f₁ = i₂ ≫ Y₂.hom ≫ Spec.map f₂ := by
    rw [← Category.assoc, h₁.w, ← Category.assoc, h₂.w, Category.assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp, hP.w]
  let y : Y ⟶ Spec P := hpo.desc (Y₁.hom ≫ Spec.map f₁) (Y₂.hom ≫ Spec.map f₂) hcomm
  obtain ⟨k₁, k₂, kf⟩ := GlobalTheory.T.flat_ferrandPushout_over_fibreProduct P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hg₁ hg₂ hn₁ hn₂ Y₁.left Y₂.left Y₀.left Y₁.hom Y₂.hom Y₀.hom i₁ i₂ h₁ h₂ hf₁ hf₂ Y j₁ j₂ hw hj₁ hj₂ hV y (hpo.inl_desc _ _ _) (hpo.inr_desc _ _ _)
  exact ⟨Over.mk y, j₁, j₂, k₁, k₂, kf, hpo⟩

end GlobalTheory.FerrandGlue
