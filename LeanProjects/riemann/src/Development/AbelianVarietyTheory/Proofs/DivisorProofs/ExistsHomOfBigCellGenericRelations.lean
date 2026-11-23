import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory

theorem groupChunk_extend {G H : Type} [Group G] [Group H] (C : G → Prop) (f : G → H)
    (hmul : ∀ x y, C x → C y → C (x * y) → f (x * y) = f x * f y)
    (hgen : ∀ s : Finset G, ∃ u : G, ∀ g ∈ s, C (g * u)) :
    ∃ Φ : G →* H, ∀ g u, C u → C (g * u) → Φ g = f (g * u) * (f u)⁻¹ := by
  classical

  have key : ∀ g u w, C u → C (g * u) → C w → C (g * w) → C (u⁻¹ * w) →
      f (g * u) * (f u)⁻¹ = f (g * w) * (f w)⁻¹ := by
    intro g u w hu hgu hw hgw huw
    have h1 : f w = f u * f (u⁻¹ * w) := by
      have h := hmul u (u⁻¹ * w) hu huw (by rwa [mul_inv_cancel_left])
      rwa [mul_inv_cancel_left] at h
    have h2 : f (g * w) = f (g * u) * f (u⁻¹ * w) := by
      have h := hmul (g * u) (u⁻¹ * w) hgu huw (by rwa [mul_assoc, mul_inv_cancel_left])
      rwa [mul_assoc, mul_inv_cancel_left] at h
    rw [h1, h2]
    group
  choose u₀ hu₀ using fun g : G => hgen {1, g}
  have hu₀1 : ∀ g, C (u₀ g) := fun g => by simpa using hu₀ g 1 (by simp)
  have hu₀g : ∀ g, C (g * u₀ g) := fun g => hu₀ g g (by simp)
  let φ : G → H := fun g => f (g * u₀ g) * (f (u₀ g))⁻¹
  have hφ : ∀ g u, C u → C (g * u) → φ g = f (g * u) * (f u)⁻¹ := by
    intro g u hu hgu
    obtain ⟨w, hw⟩ := hgen {1, g, u⁻¹, (u₀ g)⁻¹}
    have hw1 : C w := by simpa using hw 1 (by simp)
    have hwg : C (g * w) := hw g (by simp)
    have hwu : C (u⁻¹ * w) := hw u⁻¹ (by simp)
    have hwu₀ : C ((u₀ g)⁻¹ * w) := hw (u₀ g)⁻¹ (by simp)
    rw [key g u w hu hgu hw1 hwg hwu]
    exact key g (u₀ g) w (hu₀1 g) (hu₀g g) hw1 hwg hwu₀
  refine ⟨MonoidHom.mk' φ ?_, fun g u hu hgu => hφ g u hu hgu⟩
  intro g h
  obtain ⟨w, hw⟩ := hgen {1, h, g * h}
  have hw1 : C w := by simpa using hw 1 (by simp)
  have hwh : C (h * w) := hw h (by simp)
  have hwgh : C (g * h * w) := hw (g * h) (by simp)
  rw [hφ (g * h) w hw1 hwgh, hφ h w hw1 hwh, hφ g (h * w) hwh (by rwa [← mul_assoc]),
    ← mul_assoc g h w]
  group

theorem bigCell_hom : ∀ (G H : Type) [Group G] [Group H] (P : Subgroup G) (w : G) (ρ : P →* H) (W : H), (∀ p q : P, w * p = q * w → W * ρ p = ρ q * W) → (∀ p : P, (∃ p₁ p₂ : P, w * p * w = p₁ * w * p₂) → ∃ p₁ p₂ : P, w * p * w = p₁ * w * p₂ ∧ W * ρ p * W = ρ p₁ * W * ρ p₂) → (∀ s : Finset G, ∃ u : G, ∀ g ∈ s, ∃ p₁ p₂ : P, g * u = p₁ * w * p₂) → ∃ Φ : G →* H, (∀ p : P, Φ p = ρ p) ∧ Φ w = W := by
  classical
  intro G H _ _ P w ρ W ha hb hc
  let C : G → Prop := fun g => ∃ p₁ p₂ : P, g = p₁ * w * p₂

  have hwd : ∀ p₁ p₂ q₁ q₂ : P, (p₁ : G) * w * p₂ = q₁ * w * q₂ →
      ρ p₁ * W * ρ p₂ = ρ q₁ * W * ρ q₂ := by
    intro p₁ p₂ q₁ q₂ h
    have h' : w * ((p₂ * q₂⁻¹ : P) : G) = ((p₁⁻¹ * q₁ : P) : G) * w := by
      push_cast
      calc w * ((p₂ : G) * (q₂ : G)⁻¹)
          = (p₁ : G)⁻¹ * ((p₁ : G) * w * p₂) * (q₂ : G)⁻¹ := by group
        _ = (p₁ : G)⁻¹ * ((q₁ : G) * w * q₂) * (q₂ : G)⁻¹ := by rw [h]
        _ = (p₁ : G)⁻¹ * q₁ * w := by group
    have h'' := ha _ _ h'
    rw [map_mul, map_mul, map_inv, map_inv] at h''
    calc ρ p₁ * W * ρ p₂ = ρ p₁ * (W * (ρ p₂ * (ρ q₂)⁻¹)) * ρ q₂ := by group
      _ = ρ p₁ * ((ρ p₁)⁻¹ * ρ q₁ * W) * ρ q₂ := by rw [h'']
      _ = ρ q₁ * W * ρ q₂ := by group
  let f : G → H := fun g => if h : C g then ρ h.choose * W * ρ h.choose_spec.choose else 1
  have hf : ∀ p₁ p₂ : P, f (p₁ * w * p₂) = ρ p₁ * W * ρ p₂ := by
    intro p₁ p₂
    have hC : C (p₁ * w * p₂) := ⟨p₁, p₂, rfl⟩
    dsimp only [f]
    rw [dif_pos hC]
    exact hwd _ _ _ _ hC.choose_spec.choose_spec.symm
  have hmul : ∀ x y, C x → C y → C (x * y) → f (x * y) = f x * f y := by
    rintro x y ⟨p₁, p₂, rfl⟩ ⟨q₁, q₂, rfl⟩ ⟨r₁, r₂, hr⟩
    have hin : ∃ a b : P, w * ((p₂ * q₁ : P) : G) * w = a * w * b :=
      ⟨p₁⁻¹ * r₁, r₂ * q₂⁻¹, by
        push_cast
        calc w * ((p₂ : G) * q₁) * w
            = (p₁ : G)⁻¹ * ((p₁ : G) * w * p₂ * ((q₁ : G) * w * q₂)) * (q₂ : G)⁻¹ := by group
          _ = (p₁ : G)⁻¹ * ((r₁ : G) * w * r₂) * (q₂ : G)⁻¹ := by rw [hr]
          _ = (p₁ : G)⁻¹ * r₁ * w * ((r₂ : G) * (q₂ : G)⁻¹) := by group⟩
    obtain ⟨a, b, hab, hW⟩ := hb _ hin
    rw [map_mul] at hW
    have hxy : (p₁ : G) * w * p₂ * ((q₁ : G) * w * q₂) = ((p₁ * a : P) : G) * w * ((b * q₂ : P) : G) := by
      calc (p₁ : G) * w * p₂ * ((q₁ : G) * w * q₂)
          = (p₁ : G) * (w * ((p₂ * q₁ : P) : G) * w) * q₂ := by push_cast; group
        _ = (p₁ : G) * ((a : G) * w * b) * q₂ := by rw [hab]
        _ = ((p₁ * a : P) : G) * w * ((b * q₂ : P) : G) := by push_cast; group
    rw [hxy, hf, hf, hf, map_mul, map_mul]
    calc ρ p₁ * ρ a * W * (ρ b * ρ q₂) = ρ p₁ * (ρ a * W * ρ b) * ρ q₂ := by group
      _ = ρ p₁ * (W * (ρ p₂ * ρ q₁) * W) * ρ q₂ := by rw [hW]
      _ = ρ p₁ * W * ρ p₂ * (ρ q₁ * W * ρ q₂) := by group
  obtain ⟨Φ, hΦ⟩ := groupChunk_extend C f hmul hc
  refine ⟨Φ, fun p => ?_, ?_⟩
  · obtain ⟨u, hu⟩ := hc {1}
    obtain ⟨a, b, hab⟩ := hu 1 (by simp)
    rw [one_mul] at hab
    have e1 : (p : G) * u = ((p * a : P) : G) * w * b := by
      rw [hab]
      push_cast
      group
    rw [hΦ p u ⟨a, b, hab⟩ ⟨p * a, b, e1⟩, e1, hab, hf, hf, map_mul]
    group
  · obtain ⟨u, hu⟩ := hc {1, w}
    obtain ⟨a, b, hab⟩ := hu 1 (by simp)
    rw [one_mul] at hab
    obtain ⟨c, d, hcd⟩ := hu w (by simp)
    have hin : ∃ p₁ p₂ : P, w * (a : G) * w = p₁ * w * p₂ :=
      ⟨c, d * b⁻¹, by
        calc w * (a : G) * w = w * u * (b : G)⁻¹ := by rw [hab]; group
          _ = (c : G) * w * d * (b : G)⁻¹ := by rw [hcd]
          _ = (c : G) * w * ((d * b⁻¹ : P) : G) := by push_cast; group⟩
    obtain ⟨r₁, r₂, hr, hW⟩ := hb a hin
    have e1 : w * u = (r₁ : G) * w * ((r₂ * b : P) : G) := by
      rw [hab]
      push_cast
      calc w * ((a : G) * w * b) = w * a * w * b := by group
        _ = (r₁ : G) * w * ((r₂ : G) * b) := by rw [hr]; group
    rw [hΦ w u ⟨a, b, hab⟩ ⟨c, d, hcd⟩, e1, hab, hf, hf, map_mul]
    calc ρ r₁ * W * (ρ r₂ * ρ b) * (ρ a * W * ρ b)⁻¹ = (ρ r₁ * W * ρ r₂) * (ρ a * W)⁻¹ := by group
      _ = (W * ρ a * W) * (ρ a * W)⁻¹ := by rw [hW]
      _ = W := by group

end GlobalTheory
