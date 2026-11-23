import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularEverywhereIsIntegralStatement
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem mem_regAt_genPt_of_isCptGen {X : Scheme.{0}} {Ω : Type} [Field Ω]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} (h : IsCptGen ξ) (a : Ω) :
    a ∈ regAt ξ ⟨genPt ξ, specializes_refl _⟩ := by
  obtain ⟨g, hg⟩ := h.bij.2 a
  refine ⟨g, ?_⟩
  rw [← hg]
  simp only [genMap, genPt, TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]
  rfl

theorem genPt_mem_genFibre_of_isCptGen {X : Scheme.{0}} {Ω : Type} [Field Ω]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} (h : IsCptGen ξ) (O : Type) [CommRing O] [Algebra O Ω]
    (hi : Function.Injective (algebraMap O Ω)) :
    (⟨genPt ξ, specializes_refl _⟩ : Cpt ξ) ∈ genFibre O ξ := fun o ho =>
  ⟨fun h0 => ho (hi (by rw [h0, map_zero])), mem_regAt_genPt_of_isCptGen h _,
    mem_regAt_genPt_of_isCptGen h _⟩

theorem mem_lat_genFibre_iff_const_mul : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s], ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → Function.Injective (algebraMap O Ω) → IsCptGen ξ → ConstClosed O Ω → ∀ (L : Lat ξ Ω) (t : Ω), (∀ p ∈ genFibre O ξ, L.IsGenAt p t) → ∀ u : Ω, (∀ p ∈ genFibre O ξ, u ∈ L p) ↔ ∃ x y : O, y ≠ 0 ∧ u * algebraMap O Ω y = algebraMap O Ω x * t := by
  intro X Ω _ ξ O _ _ _ s _ hs hi hξ hc L t ht u
  have ht0 : t ≠ 0 := (ht _ (genPt_mem_genFibre_of_isCptGen hξ O hi)).1
  constructor
  · intro hu
    have hreg : ∀ p ∈ genFibre O ξ, u / t ∈ regAt ξ p := by
      intro p hp
      have h1 := hu p hp
      rw [(ht p hp).2] at h1
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h1
      replace hc : (c : Ω) * t = u := hc
      rw [← hc, mul_div_cancel_right₀ _ ht0]
      exact c.2
    obtain ⟨x, y, hy, e⟩ := hc _ ((GlobalTheory.T.regular_everywhere_isIntegral X Ω ξ O s hs hi hξ (u / t)).2 hreg)
    refine ⟨x, y, hy, ?_⟩
    rw [← e]
    field_simp
  · rintro ⟨x, y, hy, e⟩ p hp
    rw [(ht p hp).2]
    have hx : algebraMap O Ω x ∈ regAt ξ p := by
      by_cases h0 : x = 0
      · rw [h0, map_zero]; exact zero_mem _
      · exact (hp x h0).2.1
    have hyu := hp y hy
    refine Submodule.mem_span_singleton.2 ⟨⟨_, mul_mem hx hyu.2.2⟩, ?_⟩
    change algebraMap O Ω x * (algebraMap O Ω y)⁻¹ * t = u
    have := hyu.1
    rw [mul_right_comm, ← e]
    field_simp

end GlobalTheory.CompanionTheory.Ar.Flat
