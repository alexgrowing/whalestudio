import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm

theorem norm_unitsChar_apply {C : Type} [CommGroup C] [Fintype C] (θ : C →* ℂˣ) (z : C) :
    ‖(θ z : ℂ)‖ = 1 := by
  have h : (θ z : ℂ) ^ Fintype.card C = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one h Fintype.card_ne_zero

theorem sum_unitsChar_mul_inv {C : Type} [CommGroup C] [Fintype C] (θ η : C →* ℂˣ) :
    ∑ z : C, (θ z : ℂ) * (η z⁻¹ : ℂ) = if θ = η then (Fintype.card C : ℂ) else 0 := by
  split_ifs with h
  · subst h
    have : ∀ z : C, (θ z : ℂ) * (θ z⁻¹ : ℂ) = 1 := by
      intro z
      rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    simp only [this]
    simp
  · have hne : (Units.coeHom ℂ).comp (θ * η⁻¹) ≠ 1 := by
      intro h1
      apply h
      ext z
      have h2 := DFunLike.congr_fun h1 z
      have h3 : θ z * (η z)⁻¹ = 1 := by
        apply Units.ext
        simpa using h2
      rw [mul_inv_eq_one] at h3
      rw [h3]
    have := sum_hom_units_eq_zero _ hne
    rw [← this]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp

theorem card_le_card_mul_card_support :
    ∀ (C : Type) [CommGroup C] [Fintype C] (S : Finset (C →* ℂˣ)) (c : (C →* ℂˣ) → ℂ), (∃ z : C, ∑ θ ∈ S, c θ * (θ z : ℂ) ≠ 0) → Fintype.card C ≤ S.card * (Finset.univ.filter fun z : C => ∑ θ ∈ S, c θ * (θ z : ℂ) ≠ 0).card := by
  intro C _ _ S c hz
  obtain ⟨z₁, hz₁⟩ := hz
  set f : C → ℂ := fun z => ∑ θ ∈ S, c θ * (θ z : ℂ) with hf
  set T : Finset C := Finset.univ.filter fun z : C => f z ≠ 0 with hT
  obtain ⟨z₀, -, hz₀⟩ := Finset.exists_max_image Finset.univ (fun z => ‖f z‖) ⟨z₁, Finset.mem_univ _⟩
  have hM : 0 < ‖f z₀‖ := lt_of_lt_of_le (norm_pos_iff.mpr hz₁) (hz₀ z₁ (Finset.mem_univ _))
  have hinv : ∀ η ∈ S, (Fintype.card C : ℂ) * c η = ∑ z ∈ T, f z * (η z⁻¹ : ℂ) := by
    intro η hη
    have h1 : ∑ z ∈ T, f z * (η z⁻¹ : ℂ) = ∑ z : C, f z * (η z⁻¹ : ℂ) := by
      rw [hT]
      refine Finset.sum_subset (Finset.filter_subset _ _) fun z _ hz => ?_
      have : f z = 0 := by simpa using hz
      rw [this, zero_mul]
    rw [h1]
    simp only [hf, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, sum_unitsChar_mul_inv, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq' S η, if_pos hη, mul_comm]
  have hc : ∀ η ∈ S, (Fintype.card C : ℝ) * ‖c η‖ ≤ T.card * ‖f z₀‖ := by
    intro η hη
    have h1 : ‖(Fintype.card C : ℂ) * c η‖ = (Fintype.card C : ℝ) * ‖c η‖ := by
      rw [norm_mul, Complex.norm_natCast]
    rw [← h1, hinv η hη]
    refine (norm_sum_le _ _).trans ?_
    rw [← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun z _ => ?_
    rw [norm_mul, norm_unitsChar_apply, mul_one]
    exact hz₀ z (Finset.mem_univ _)
  have hf0 : ‖f z₀‖ ≤ ∑ η ∈ S, ‖c η‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun η _ => ?_
    rw [norm_mul, norm_unitsChar_apply, mul_one]
  have hfin : (Fintype.card C : ℝ) * ‖f z₀‖ ≤ ((S.card : ℝ) * T.card) * ‖f z₀‖ := by
    calc (Fintype.card C : ℝ) * ‖f z₀‖ ≤ (Fintype.card C : ℝ) * ∑ η ∈ S, ‖c η‖ :=
          mul_le_mul_of_nonneg_left hf0 (Nat.cast_nonneg _)
      _ = ∑ η ∈ S, (Fintype.card C : ℝ) * ‖c η‖ := Finset.mul_sum _ _ _
      _ ≤ S.card • ((T.card : ℝ) * ‖f z₀‖) := Finset.sum_le_card_nsmul _ _ _ hc
      _ = _ := by rw [nsmul_eq_mul, mul_assoc]
  have := le_of_mul_le_mul_right hfin hM
  exact_mod_cast this

end GlobalTheory.GLm
