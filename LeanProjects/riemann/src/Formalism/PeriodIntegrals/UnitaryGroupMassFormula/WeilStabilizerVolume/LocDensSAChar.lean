import Mathlib

noncomputable section

open NumberField

namespace PI.VolStabW

def ChInf : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Λ : Submodule (𝓞 F) F), (∃ c : F, c ≠ 0 ∧ c ∈ Λ) →
    (∀ c : F, c ≠ 0 → ¬ ∀ a ∈ Λ, ∃ r : 𝓞 F, a = c * r) →
    ∀ χ : AddChar (InfiniteAdeleRing F) ℂ, Continuous χ →
    (∀ a ∈ Λ, χ (algebraMap F (InfiniteAdeleRing F) a) = 1) → ∀ x, χ x = 1

def ChLift : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : AddChar (InfiniteAdeleRing F) ℂ), Continuous χ →
    ∃ ℓ : InfiniteAdeleRing F →+ ℂ, Continuous ℓ ∧ ∀ x, χ x = Complex.exp (ℓ x)

def AddIntF : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Λ : Submodule (𝓞 F) F), (∃ c : F, c ≠ 0 ∧ c ∈ Λ) →
    (∀ c : F, c ≠ 0 → ¬ ∀ a ∈ Λ, ∃ r : 𝓞 F, a = c * r) →
    ∀ g : F →+ ℂ, (∀ a ∈ Λ, ∃ n : ℤ, g a = n) → ∀ a, g a = 0

theorem chInf_of (hL : ChLift) (hA : AddIntF) : ChInf := by
  intro F _ _ Λ h0 hb χ hχ hΛ x
  obtain ⟨ℓ, hℓc, hℓ⟩ := hL F χ hχ
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  let g : F →+ ℂ :=
    { toFun := fun a => ℓ (algebraMap F (InfiniteAdeleRing F) a) / (2 * Real.pi * Complex.I)
      map_zero' := by simp
      map_add' := fun a b => by simp [add_div] }
  have hg : ∀ a ∈ Λ, ∃ n : ℤ, g a = n := fun a ha => by
    have := hΛ a ha
    rw [hℓ, Complex.exp_eq_one_iff] at this
    obtain ⟨n, hn⟩ := this
    exact ⟨n, by simp only [g, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hn]; field_simp⟩
  have hg0 := hA F Λ h0 hb g hg
  have hz : ∀ a : F, ℓ (algebraMap F (InfiniteAdeleRing F) a) = 0 := fun a => by
    have := hg0 a
    simp only [g, AddMonoidHom.coe_mk, ZeroHom.coe_mk, div_eq_zero_iff, h2, or_false] at this
    exact this
  have : ℓ x = 0 := (InfiniteAdeleRing.denseRange_algebraMap F).induction_on x
    (isClosed_eq hℓc continuous_const) hz
  rw [hℓ, this, Complex.exp_zero]

end PI.VolStabW
