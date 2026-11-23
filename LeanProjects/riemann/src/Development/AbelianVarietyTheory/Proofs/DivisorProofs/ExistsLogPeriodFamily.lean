import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntBTmulBasis
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

theorem GlobalTheory.AbsLattice.exists_unit_of_conj_stable : ∀ {A B : Type} [Ring A] [CommRing B] (j : B →+* A) (Λ : Set A) (R : Set B) (r : ℕ) (e : Fin r → A),
    (0 : A) ∈ Λ → (1 : A) ∈ Λ → (∀ x ∈ Λ, ∀ y ∈ Λ, x + y ∈ Λ) → (∀ x ∈ Λ, -x ∈ Λ) →
    (∀ x ∈ Λ, ∀ y ∈ Λ, x * y ∈ Λ) →
    (0 : B) ∈ R → (1 : B) ∈ R → (∀ x ∈ R, ∀ y ∈ R, x + y ∈ R) → (∀ x ∈ R, -x ∈ R) →
    (∀ x ∈ R, ∀ y ∈ R, x * y ∈ R) →
    (∀ a : A, ∃! β : Fin r → B, a = ∑ i, j (β i) * e i) →
    (∀ β : Fin r → B, (∑ i, j (β i) * e i ∈ Λ) ↔ ∀ i, β i ∈ R) →
    (∀ i i' : Fin r, ∃ (N : ℕ) (ρ : Fin N → B) (μ : Fin N → A), (∀ k, ρ k ∈ R) ∧ (∀ k, μ k ∈ Λ) ∧
      ∀ β : Fin r → B, ∑ k, j (ρ k) * (∑ i'', j (β i'') * e i'') * μ k = j (β i') * e i) →
    (∀ a : A, ∃ D : ℤ, D ≠ 0 ∧ (D : A) * a ∈ Λ) →
    (∀ I : Set B, (0 : B) ∈ I → (∀ x ∈ I, ∀ y ∈ I, x + y ∈ I) → (∀ ρ ∈ R, ∀ x ∈ I, ρ * x ∈ I) →
      (∃ D : ℤ, D ≠ 0 ∧ (∀ x ∈ R, (D : B) * x ∈ I) ∧ ∀ x ∈ I, (D : B) * x ∈ R) →
      ∃ m : Bˣ, ∀ x, x ∈ I ↔ ∃ ρ ∈ R, x = ↑m * ρ) →
    ∀ X : Aˣ, (∀ ρ ∈ R, (X : A) * j ρ * ↑X⁻¹ ∈ Λ) → ∃ m : Bˣ, (X : A) * j ↑m ∈ Λ ∧ j ↑m⁻¹ * ↑X⁻¹ ∈ Λ := by

  intro A B _ _ j Λ R r e h0 h1 hadd hneg hmul hR0 hR1 hRadd hRneg hRmul hrep hmem hE hden hsq X hX
  rcases r with _ | n
  · have hall : ∀ a : A, a = 0 := fun a => by
      obtain ⟨β, hβ, -⟩ := hrep a
      simpa using hβ
    have key : ∀ a : A, a ∈ Λ := fun a => by rw [hall a]; exact h0
    exact ⟨1, key _, key _⟩
  ·
    have hL : ∀ ρ ∈ R, ∀ x : A, (X : A) * x ∈ Λ → (X : A) * (j ρ * x) ∈ Λ := by
      intro ρ hρ x hx
      have : (X : A) * (j ρ * x) = ((X : A) * j ρ * ↑X⁻¹) * ((X : A) * x) := by
        simp [mul_assoc]
      rw [this]; exact hmul _ (hX ρ hρ) _ hx
    have hRt : ∀ μ ∈ Λ, ∀ x : A, (X : A) * x ∈ Λ → (X : A) * (x * μ) ∈ Λ := by
      intro μ hμ x hx
      rw [← mul_assoc]; exact hmul _ hx _ hμ
    have hS : ∀ (N : ℕ) (f : Fin N → A), (∀ k, (X : A) * f k ∈ Λ) → (X : A) * ∑ k, f k ∈ Λ := by
      intro N f hf
      rw [Finset.mul_sum]
      exact Finset.sum_induction _ (· ∈ Λ) (fun a b ha hb => hadd a ha b hb) h0 (fun k _ => hf k)
    have hsingle : ∀ b : B, ∑ i'', j ((Pi.single (0 : Fin (n+1)) b : Fin (n+1) → B) i'') * e i'' = j b * e 0 := by
      intro b
      rw [Finset.sum_eq_single 0]
      · simp
      · intro i _ hi
        rw [Pi.single_eq_of_ne hi, map_zero, zero_mul]
      · simp
    have hsingleR : ∀ b : B, j b * e 0 ∈ Λ ↔ b ∈ R := by
      intro b
      rw [← hsingle, hmem]
      constructor
      · intro h; simpa using h 0
      · intro hb i
        by_cases hi : i = 0
        · subst hi; simpa using hb
        · rw [Pi.single_eq_of_ne hi]; exact hR0
    have he0 : e 0 ∈ Λ := by
      have := (hsingleR 1).2 hR1
      rwa [map_one, one_mul] at this

    have hA : ∀ β : Fin (n+1) → B, (X : A) * (∑ i, j (β i) * e i) ∈ Λ →
        ∀ i', (X : A) * (j (β i') * e 0) ∈ Λ := by
      intro β hx i'
      obtain ⟨N, ρ, μ, hρ, hμ, hf⟩ := hE 0 i'
      rw [← hf β]
      exact hS N _ (fun k => hRt (μ k) (hμ k) _ (hL _ (hρ k) _ hx))

    have hB : ∀ b : B, (X : A) * (j b * e 0) ∈ Λ → ∀ i, (X : A) * (j b * e i) ∈ Λ := by
      intro b hb i
      obtain ⟨N, ρ, μ, hρ, hμ, hf⟩ := hE i 0
      have h := hf (Pi.single 0 b)
      rw [hsingle, Pi.single_eq_same] at h
      rw [← h]
      exact hS N _ (fun k => hRt (μ k) (hμ k) _ (hL _ (hρ k) _ hb))
    have hsum : ∀ β : Fin (n+1) → B, (∀ i, (X : A) * (j (β i) * e 0) ∈ Λ) →
        (X : A) * (∑ i, j (β i) * e i) ∈ Λ :=
      fun β hβ => hS _ _ (fun i => hB _ (hβ i) i)
    have hRint : ∀ z : ℤ, (z : B) ∈ R := by
      intro z
      induction z using Int.induction_on with
      | zero => simpa using hR0
      | succ i ih => rw [Int.cast_add, Int.cast_one]; exact hRadd _ ih _ hR1
      | pred i ih =>
        have : ((-(i : ℤ) - 1 : ℤ) : B) = ((-(i : ℤ) : ℤ) : B) + -1 := by push_cast; ring
        rw [this]; exact hRadd _ ih _ (hRneg _ hR1)
    obtain ⟨D₁, hD₁, hD₁m⟩ := hden (X : A)
    obtain ⟨D₂, hD₂, hD₂m⟩ := hden (↑X⁻¹ : A)
    have hDR : ∀ ρ ∈ R, (X : A) * (j (ρ * D₁) * e 0) ∈ Λ := by
      intro ρ hρ
      rw [map_mul, map_intCast, mul_assoc]
      apply hL ρ hρ
      rw [← mul_assoc, ← (Int.cast_commute D₁ (X : A)).eq]
      exact hmul _ hD₁m _ he0
    have hDI : ∀ β : B, (X : A) * (j β * e 0) ∈ Λ → β * D₂ ∈ R := by
      intro β hβ
      rw [← hsingleR]
      have : j (β * D₂) * e 0 = ((D₂ : A) * ↑X⁻¹) * ((X : A) * (j β * e 0)) := by
        rw [map_mul, map_intCast, ← (Int.cast_commute D₂ (j β)).eq, mul_assoc, mul_assoc,
          Units.inv_mul_cancel_left]
      rw [this]; exact hmul _ hD₂m _ hβ
    obtain ⟨m, hm⟩ := hsq {β | (X : A) * (j β * e 0) ∈ Λ}
      (by show (X : A) * (j 0 * e 0) ∈ Λ; simpa using h0)
      (fun x hx y hy => by
        show (X : A) * (j (x + y) * e 0) ∈ Λ
        rw [map_add, add_mul, mul_add]; exact hadd _ hx _ hy)
      (fun ρ hρ x hx => by
        show (X : A) * (j (ρ * x) * e 0) ∈ Λ
        rw [map_mul, mul_assoc]; exact hL ρ hρ _ hx)
      ⟨D₁ * D₂, mul_ne_zero hD₁ hD₂,
        fun x hx => by
          show (X : A) * (j (((D₁ * D₂ : ℤ) : B) * x) * e 0) ∈ Λ
          have : ((D₁ * D₂ : ℤ) : B) * x = (D₂ : B) * (x * D₁) := by push_cast; ring
          rw [this, map_mul, mul_assoc]
          exact hL _ (hRint D₂) _ (hDR x hx),
        fun x hx => by
          have : ((D₁ * D₂ : ℤ) : B) * x = (D₁ : B) * (x * D₂) := by push_cast; ring
          rw [this]
          exact hRmul _ (hRint D₁) _ (hDI x hx)⟩
    refine ⟨m, ?_, ?_⟩
    · obtain ⟨γ, hγ, -⟩ := hrep 1
      have hγR : ∀ i, γ i ∈ R := (hmem γ).1 (hγ ▸ h1)
      have hjm : j (m : B) = ∑ i, j ((m : B) * γ i) * e i := by
        conv_lhs => rw [← mul_one (j (m : B)), hγ]
        rw [Finset.mul_sum]
        simp only [map_mul, mul_assoc]
      rw [hjm]
      exact hsum _ (fun i => (hm _).2 ⟨γ i, hγR i, rfl⟩)
    · obtain ⟨β, hβ, -⟩ := hrep (↑X⁻¹ : A)
      have hXinv : (X : A) * (∑ i, j (β i) * e i) ∈ Λ := by
        rw [← hβ, Units.mul_inv]; exact h1
      have hc : ∀ i, ∃ ρ ∈ R, β i = (m : B) * ρ := fun i => (hm _).1 (hA β hXinv i)
      choose ρ hρR hρeq using hc
      have : j (↑m⁻¹ : B) * (↑X⁻¹ : A) = ∑ i, j (ρ i) * e i := by
        rw [hβ, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [← mul_assoc, ← map_mul, hρeq, ← mul_assoc, Units.inv_mul, one_mul]
      rw [this]; exact (hmem ρ).2 hρR
