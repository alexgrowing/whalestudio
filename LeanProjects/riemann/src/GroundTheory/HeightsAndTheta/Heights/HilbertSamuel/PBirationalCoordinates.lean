import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBirationalCoordinatesA
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace BirationalCoordinates

section Ratios

variable {Ω : Type} [Field Ω] {κ : Type} [Fintype κ]

def ratioField (x : Ix κ → Ω) (c : κ) : Subfield Ω :=
  Subfield.closure (Set.range fun p : Ix κ => x p / x ⟨(), c⟩)

def ratios (x : Ix κ → Ω) (c : κ) : Ix κ → ratioField x c := fun p =>
  ⟨x p / x ⟨(), c⟩, Subfield.subset_closure ⟨p, rfl⟩⟩

omit [Fintype κ] in
theorem ratios_c (x : Ix κ → Ω) {c : κ} (hc : x ⟨(), c⟩ ≠ 0) : ratios x c ⟨(), c⟩ = 1 :=
  Subtype.ext (div_self hc)

omit [Fintype κ] in
theorem eq_mul_ratios (x : Ix κ → Ω) {c : κ} (hc : x ⟨(), c⟩ ≠ 0) (p : Ix κ) :
    x p = x ⟨(), c⟩ * (ratioField x c).subtype (ratios x c p) := by
  change x p = x ⟨(), c⟩ * (x p / x ⟨(), c⟩)
  rw [mul_div_cancel₀ _ hc]

theorem birational_ratios (x : Ix κ → Ω) {c : κ} (hc : x ⟨(), c⟩ ≠ 0) :
    Birational (ι := GlobalTheory κ) (ratios x c) := by
  intro s
  obtain ⟨s, hs⟩ := s
  induction hs using Subfield.closure_induction with
  | mem t ht =>
    obtain ⟨p, rfl⟩ := ht
    refine ⟨fun _ => 1, X p, X ⟨(), c⟩, ?_, ?_, ?_, ?_⟩
    · convert ProjLine.isMultiHomog_X (ι := GlobalTheory κ) p using 1
      funext k
      simp
    · convert ProjLine.isMultiHomog_X (ι := GlobalTheory κ) ⟨(), c⟩ using 1
      funext k
      simp
    · rw [aeval_X, ratios_c x hc]
      exact one_ne_zero
    · rw [aeval_X, aeval_X, ratios_c x hc, mul_one]
      rfl
  | one =>
    refine ⟨0, 1, 1, ProjLine.isMultiHomog_one, ProjLine.isMultiHomog_one, by simp, ?_⟩
    simp only [map_one, mul_one]
    rfl
  | add a b ha hb iha ihb =>
    obtain ⟨d₁, g₁, h₁, hg₁, hh₁, hne₁, he₁⟩ := iha
    obtain ⟨d₂, g₂, h₂, hg₂, hh₂, hne₂, he₂⟩ := ihb
    have hsum : IsMultiHomog (g₁ * h₂ + g₂ * h₁) (d₁ + d₂) := by
      refine ProjLine.mhAdd (ProjLine.mhMul hg₁ hh₂) ?_
      rw [add_comm d₁]
      exact ProjLine.mhMul hg₂ hh₁
    refine ⟨d₁ + d₂, g₁ * h₂ + g₂ * h₁, h₁ * h₂, hsum, ProjLine.mhMul hh₁ hh₂, ?_, ?_⟩
    · rw [map_mul]
      exact mul_ne_zero hne₁ hne₂
    · rw [map_add, map_mul, map_mul, map_mul, he₁, he₂]
      have : (⟨a + b, add_mem ha hb⟩ : ratioField x c) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
      rw [this]
      ring
  | neg a ha iha =>
    obtain ⟨d, g, h, hg, hh, hne, he⟩ := iha
    refine ⟨d, -g, h, ProjLine.mhNeg hg, hh, hne, ?_⟩
    rw [map_neg, he]
    have : (⟨-a, neg_mem ha⟩ : ratioField x c) = -⟨a, ha⟩ := rfl
    rw [this]
    ring
  | inv a ha iha =>
    obtain ⟨d, g, h, hg, hh, hne, he⟩ := iha
    by_cases ha0 : (⟨a, ha⟩ : ratioField x c) = 0
    · refine ⟨0, 0, 1, ProjLine.isMultiHomog_zero _, ProjLine.isMultiHomog_one, by simp, ?_⟩
      have : (⟨a⁻¹, inv_mem ha⟩ : ratioField x c) = (⟨a, ha⟩ : ratioField x c)⁻¹ := rfl
      rw [this, ha0]
      simp
    · have hg0 : aeval (ratios x c) g ≠ 0 := by
        rw [he]
        exact mul_ne_zero ha0 hne
      refine ⟨d, h, g, hh, hg, hg0, ?_⟩
      have : (⟨a⁻¹, inv_mem ha⟩ : ratioField x c) = (⟨a, ha⟩ : ratioField x c)⁻¹ := rfl
      rw [this, he]
      field_simp
  | mul a b ha hb iha ihb =>
    obtain ⟨d₁, g₁, h₁, hg₁, hh₁, hne₁, he₁⟩ := iha
    obtain ⟨d₂, g₂, h₂, hg₂, hh₂, hne₂, he₂⟩ := ihb
    refine ⟨d₁ + d₂, g₁ * g₂, h₁ * h₂, ProjLine.mhMul hg₁ hg₂, ProjLine.mhMul hh₁ hh₂, ?_, ?_⟩
    · rw [map_mul]
      exact mul_ne_zero hne₁ hne₂
    · rw [map_mul, map_mul, he₁, he₂]
      have : (⟨a * b, mul_mem ha hb⟩ : ratioField x c) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
      rw [this]
      ring

end Ratios

theorem proof : Statement := by
  intro Ω _ _ κ _ x c hc
  have hx := eq_mul_ratios x hc
  refine ⟨ratioField x c, inferInstance, inferInstance, ratios x c,
    mCoordIdeal_eq (ratioField x c).subtype hc hx, birational_ratios x hc,
    fun A τ => smallSectionCount_eq_of_birational (ratioField x c).subtype hc hx hc A τ⟩

end BirationalCoordinates

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
