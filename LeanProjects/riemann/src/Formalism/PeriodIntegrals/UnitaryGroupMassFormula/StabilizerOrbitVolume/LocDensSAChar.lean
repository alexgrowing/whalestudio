import Mathlib

noncomputable section

open NumberField

namespace PI.VolStabSW

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
  intro F _ _ Λ hne hnd χ hχ h1 x
  obtain ⟨ℓ, hℓc, hℓ⟩ := hL F χ hχ
  have hI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  let g : F →+ ℂ := AddMonoidHom.mk' (fun a => ℓ (algebraMap F (InfiniteAdeleRing F) a) /
    (2 * Real.pi * Complex.I)) (by intro a b; simp only [map_add, add_div])
  have hint : ∀ a ∈ Λ, ∃ n : ℤ, g a = n := by
    intro a ha
    have he : Complex.exp (ℓ (algebraMap F (InfiniteAdeleRing F) a)) = 1 := by
      rw [← hℓ]
      exact h1 a ha
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp he
    refine ⟨n, ?_⟩
    show ℓ (algebraMap F (InfiniteAdeleRing F) a) / (2 * Real.pi * Complex.I) = n
    rw [hn, mul_div_assoc, div_self hI, mul_one]
  have hg := hA F Λ hne hnd g hint
  have hzero : ∀ a : F, ℓ (algebraMap F (InfiniteAdeleRing F) a) = 0 := by
    intro a
    have h := hg a
    change ℓ (algebraMap F (InfiniteAdeleRing F) a) / (2 * Real.pi * Complex.I) = 0 at h
    rcases div_eq_zero_iff.mp h with h | h
    · exact h
    · exact absurd h hI
  have hdense : DenseRange (algebraMap F (InfiniteAdeleRing F)) := by
    first
      | exact InfiniteAdeleRing.denseRange_algebraMap F
      | exact InfiniteAdeleRing.denseRange_algebraMap
      | exact NumberField.InfiniteAdeleRing.denseRange_algebraMap F
  have hx : ℓ x = 0 :=
    hdense.induction_on x (isClosed_eq hℓc continuous_const) hzero
  rw [hℓ, hx, Complex.exp_zero]

end PI.VolStabSW
