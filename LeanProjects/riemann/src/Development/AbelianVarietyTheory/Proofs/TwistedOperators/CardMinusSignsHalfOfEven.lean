import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
open Formalism.L2.Theta

namespace GlobalTheory.SignedHC

open Finset

theorem card_minus_of_isEnum {n : ℕ} {S : Finset (ℚ × Bool)} {lam : Fin n → ℝ} {ε : Fin n → Bool} (h : IsEnum S lam ε) :
    (univ.filter fun a => ε a = false).card = nMinus S := by
  obtain ⟨hanti, f, hf, rfl⟩ := h
  have hinj : Function.Injective f := fun a b h => hanti.injective (by rw [hf, hf, h])
  rw [nMinus, filter_image, card_image_of_injective _ fun a b h => hinj (congrArg Prod.fst h)]

namespace GridData

theorem nMinus_lam_of_even (G : GridData) (hm : Even G.m) (hg : 0 < G.ga) : nMinus G.lam = G.m / 2 := by
  obtain ⟨k, hk⟩ := hm
  have hS : G.lam.filter (fun x => x.2 = false) = (range k).image fun j => (G.a (2 * j + 1), false) := by
    ext x
    simp only [mem_filter, mem_lam, mem_image, mem_range]
    constructor
    · rintro ⟨⟨i, hi, rfl⟩ | ⟨-, h⟩, h2⟩
      · simp only [decide_eq_false_iff_not, Nat.not_even_iff] at h2
        refine ⟨i / 2, by omega, ?_⟩
        have e : 2 * (i / 2) + 1 = i := by omega
        have : ¬ Even (G.m - i) := by rw [Nat.not_even_iff]; exact h2
        simp [e, this]
      · simp [h] at h2
    · rintro ⟨j, hj, rfl⟩
      have : ¬ Even (G.m - (2 * j + 1)) := by rw [Nat.not_even_iff]; omega
      exact ⟨Or.inl ⟨2 * j + 1, by omega, by simp [this]⟩, rfl⟩
  rw [nMinus, hS, card_image_of_injective, card_range]
  · omega
  · intro i j h
    have h1 : G.a (2 * i + 1) = G.a (2 * j + 1) := congrArg Prod.fst h
    have h2 := G.a_sub_a (2 * i + 1) (2 * j + 1)
    rw [h1, sub_self] at h2
    have hg' : (G.ga : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
    have h3 := sub_eq_zero.1 ((mul_eq_zero.1 h2.symm).resolve_right hg')
    have h4 : 2 * j + 1 = 2 * i + 1 := by exact_mod_cast h3
    omega

theorem minus_signs_of_D0_eq_half (G : GridData) : nMinus G.parD0 = G.m / 2 := by
  have hS : G.parD0.filter (fun x => x.2 = false) =
      (range (G.m / 2)).image fun j => (-(G.b (2 * j + 2) : ℚ), false) := by
    ext x
    simp only [mem_filter, mem_discrete_parameter_iff, mem_image, mem_range]
    constructor
    · rintro ⟨⟨-, h⟩ | ⟨i, hi, hi', rfl⟩, h2⟩
      · simp [h] at h2
      · simp only [decide_eq_false_iff_not, Nat.not_even_iff] at h2
        refine ⟨i / 2 - 1, by omega, ?_⟩
        have e : 2 * (i / 2 - 1) + 2 = i := by omega
        have : ¬ Even (i - 1) := by rw [Nat.not_even_iff]; exact h2
        simp [e, this]
    · rintro ⟨j, hj, rfl⟩
      have : ¬ Even (2 * j + 2 - 1) := by rw [Nat.not_even_iff]; omega
      exact ⟨Or.inr ⟨2 * j + 2, by omega, by omega, by rw [decide_eq_false this]⟩, rfl⟩
  rw [nMinus, hS, card_image_of_injOn, card_range]
  intro i hi j hj h
  have h1 : -(G.b (2 * i + 2) : ℚ) = -(G.b (2 * j + 2) : ℚ) := congrArg Prod.fst h
  have h2 : G.b (2 * i + 2) = G.b (2 * j + 2) := by exact_mod_cast neg_injective h1
  have hi' : i < G.m / 2 := by simpa using hi
  have hj' : j < G.m / 2 := by simpa using hj
  rcases lt_trichotomy i j with hl | hl | hl
  · have := G.b_mono (2 * i + 2) (2 * j + 2) (by omega) (by omega) (by omega); omega
  · exact hl
  · have := G.b_mono (2 * j + 2) (2 * i + 2) (by omega) (by omega) (by omega); omega

theorem card_minus_signs_interlacing_parameters {G : GridData} {n : ℕ} {lam : Fin (n + 1) → ℝ} {ε : Fin (n + 1) → Bool}
    {mu : Fin n → ℝ} {ε' : Fin n → Bool} (hm : Even G.m) (hg : 0 < G.ga) (h1 : IsEnum (G.parPi 0) lam ε)
    (h2 : IsEnum G.parD0 mu ε') :
    (Finset.univ.filter fun a => ε a = false).card = G.m / 2 ∧
      (Finset.univ.filter fun i => ε' i = false).card = G.m / 2 :=
  ⟨by rw [card_minus_of_isEnum h1, G.parPi_zero, G.nMinus_lam_of_even hm hg],
    by rw [card_minus_of_isEnum h2, G.minus_signs_of_D0_eq_half]⟩

end GridData

end GlobalTheory.SignedHC
