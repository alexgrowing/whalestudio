import Mathlib

open Polynomial

theorem UpperTheory.exists_twistedTrace_eq_one_of_residueFrobenius :
    ∀ (O F₀ F₁ : Type) [CommRing O] [Field F₀] [Fintype F₀] [Field F₁] [Fintype F₁] [Algebra F₀ F₁] (r : O →+* F₁) (σ : O ≃+* O) (sb : F₁ ≃ₐ[F₀] F₁), Function.Surjective r → (∀ x, r x ≠ 0 → IsUnit x) → (∀ x, r (σ x) = sb (r x)) → (∀ z, sb z = z ^ Fintype.card F₀) → (∀ x, σ^[Module.finrank F₀ F₁] x = x) → ∃ a : O, ∑ i ∈ Finset.range (Module.finrank F₀ F₁), σ^[i] a = 1 := by
  intro O F₀ F₁ _ _ _ _ _ _ r σ sb hr hu hσ hsb hn
  set n := Module.finrank F₀ F₁ with hn_def
  have hex : ∃ b : F₁, Algebra.trace F₀ F₁ b ≠ 0 := by
    by_contra! h
    exact one_ne_zero ((traceForm_nondegenerate F₀ F₁).1 1
      (fun b => by simpa [Algebra.traceForm_apply] using h b))
  obtain ⟨b, hb⟩ := hex
  set y : F₁ := (Algebra.trace F₀ F₁ b)⁻¹ • b with hy_def
  have hty : Algebra.trace F₀ F₁ y = 1 := by
    rw [hy_def, LinearMap.map_smul, smul_eq_mul, inv_mul_cancel₀ hb]
  have hsbit : ∀ i (z : F₁), sb^[i] z = z ^ (Fintype.card F₀ ^ i) := by
    intro i
    induction i with
    | zero => intro z; simp
    | succ k ih =>
      intro z
      rw [Function.iterate_succ_apply', ih, hsb, ← pow_mul, pow_succ]
  have hsumy : ∑ i ∈ Finset.range n, sb^[i] y = 1 := by
    have h := FiniteField.algebraMap_trace_eq_sum_pow F₀ F₁ y
    rw [hty, map_one, Nat.card_eq_fintype_card] at h
    rw [h]
    exact Finset.sum_congr rfl (fun i _ => hsbit i y)
  obtain ⟨a, ha⟩ := hr y
  have hrit : ∀ i x, r (σ^[i] x) = sb^[i] (r x) := by
    intro i
    induction i with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hσ, ih]
  set s := ∑ i ∈ Finset.range n, σ^[i] a with hs_def
  have hrs : r s = 1 := by
    rw [hs_def, map_sum]
    simp_rw [hrit, ha]
    exact hsumy
  have hsunit : IsUnit s := hu s (by rw [hrs]; exact one_ne_zero)
  have hσs : σ s = s := by
    rw [hs_def, map_sum]
    have h1 : ∀ i, σ (σ^[i] a) = σ^[i + 1] a := fun i => (Function.iterate_succ_apply' σ i a).symm
    simp_rw [h1]
    have e1 := Finset.sum_range_succ' (fun i => σ^[i] a) n
    have e2 := Finset.sum_range_succ (fun i => σ^[i] a) n
    rw [e1, hn] at e2
    simp only [Function.iterate_zero, id] at e2
    exact add_right_cancel e2
  have hmul : ∀ i (x z : O), σ^[i] (x * z) = σ^[i] x * σ^[i] z := by
    intro i
    induction i with
    | zero => intro x z; simp
    | succ k ih =>
      intro x z
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_mul]
  obtain ⟨u, hu'⟩ := hsunit
  have hfix : σ (↑u⁻¹ : O) = ↑u⁻¹ := by
    have hσu : σ (↑u : O) = ↑u := by rw [hu']; exact hσs
    have : σ (↑u : O) * σ (↑u⁻¹ : O) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    rw [hσu] at this
    calc σ (↑u⁻¹ : O) = ↑u⁻¹ * (↑u * σ (↑u⁻¹ : O)) := by rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = ↑u⁻¹ := by rw [this, mul_one]
  refine ⟨a * ↑u⁻¹, ?_⟩
  have hfixit : ∀ i, σ^[i] (↑u⁻¹ : O) = ↑u⁻¹ := fun i => Function.iterate_fixed hfix i
  simp_rw [hmul, hfixit]
  rw [← Finset.sum_mul, ← hs_def, ← hu', Units.mul_inv]
