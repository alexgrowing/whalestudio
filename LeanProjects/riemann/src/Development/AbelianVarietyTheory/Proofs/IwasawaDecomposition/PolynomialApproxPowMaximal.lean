import Mathlib
open IsLocalRing

namespace GlobalTheory

theorem exists_eval₂_approx_maximalIdeal_pow_succ {A R : Type} [CommRing A] [IsLocalRing A]
    [CommRing R] [IsLocalRing R]
    (φ : A →+* R) (hm : (maximalIdeal A).map φ = maximalIdeal R) (θ : R)
    (h1 : ∀ r : R, ∃ P : Polynomial A, r - Polynomial.eval₂ φ θ P ∈ maximalIdeal R)
    (n : ℕ) (x : R) (hx : x ∈ maximalIdeal R ^ n) :
    ∃ P : Polynomial A, Polynomial.eval₂ φ θ P ∈ maximalIdeal R ^ n ∧
      x - Polynomial.eval₂ φ θ P ∈ maximalIdeal R ^ (n + 1) := by
  have hpow : maximalIdeal R ^ n = (maximalIdeal A ^ n).map φ := by
    rw [Ideal.map_pow, hm]
  rw [hpow] at hx
  unfold Ideal.map at hx
  refine Submodule.span_induction (p := fun x _ => ∃ P : Polynomial A,
      Polynomial.eval₂ φ θ P ∈ maximalIdeal R ^ n ∧
      x - Polynomial.eval₂ φ θ P ∈ maximalIdeal R ^ (n + 1)) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨a, ha, rfl⟩
    refine ⟨Polynomial.C a, ?_, ?_⟩
    · rw [Polynomial.eval₂_C, hpow]; exact Ideal.mem_map_of_mem φ ha
    · simp
  · exact ⟨0, by simp, by simp⟩
  · rintro x y _ _ ⟨P, hP, hxP⟩ ⟨Q, hQ, hyQ⟩
    refine ⟨P + Q, ?_, ?_⟩
    · rw [Polynomial.eval₂_add]; exact add_mem hP hQ
    · have : x + y - Polynomial.eval₂ φ θ (P + Q) =
          (x - Polynomial.eval₂ φ θ P) + (y - Polynomial.eval₂ φ θ Q) := by
        rw [Polynomial.eval₂_add]; ring
      rw [this]; exact add_mem hxP hyQ
  · rintro r x _ ⟨P, hP, hxP⟩
    obtain ⟨Q, hQ⟩ := h1 r
    refine ⟨Q * P, ?_, ?_⟩
    · rw [Polynomial.eval₂_mul]; exact Ideal.mul_mem_left _ _ hP
    · have : r • x - Polynomial.eval₂ φ θ (Q * P) =
          r * (x - Polynomial.eval₂ φ θ P) +
            (r - Polynomial.eval₂ φ θ Q) * Polynomial.eval₂ φ θ P := by
        rw [Polynomial.eval₂_mul, smul_eq_mul]; ring
      rw [this]
      refine add_mem (Ideal.mul_mem_left _ _ hxP) ?_
      rw [pow_succ']
      exact Ideal.mul_mem_mul hQ hP

theorem exists_poly_sub_mem_maximalIdeal_pow : ∀ {A R : Type} [CommRing A] [IsLocalRing A]
    [CommRing R] [IsLocalRing R] (φ : A →+* R), (maximalIdeal A).map φ = maximalIdeal R →
    ∀ θ : R, (∀ r : R, ∃ P : Polynomial A, r - (P.map φ).eval θ ∈ maximalIdeal R) →
    ∀ (n : ℕ) (r : R), ∃ P : Polynomial A, r - (P.map φ).eval θ ∈ maximalIdeal R ^ n := by
  intro A R _ _ _ _ φ hm θ h1 n r
  simp only [Polynomial.eval_map] at h1 ⊢
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨P, hP⟩ := ih
    obtain ⟨Q, -, hQ⟩ := exists_eval₂_approx_maximalIdeal_pow_succ φ hm θ h1 n _ hP
    refine ⟨P + Q, ?_⟩
    have : r - Polynomial.eval₂ φ θ (P + Q) =
        r - Polynomial.eval₂ φ θ P - Polynomial.eval₂ φ θ Q := by
      rw [Polynomial.eval₂_add]; ring
    rw [this]; exact hQ

end GlobalTheory
