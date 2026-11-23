import Mathlib
open scoped TensorProduct Classical

namespace GlobalTheory.PadicTensorApprox

variable {E : Type} [CommRing E] [Algebra ℚ E] {ℓ : ℕ} [Fact ℓ.Prime]

theorem isIntegral_tmul (u : ℚ_[ℓ]) (hu : ‖u‖ ≤ 1) (c : E) (hc : IsIntegral ℤ c) :
    IsIntegral ℤ_[ℓ] (u ⊗ₜ[ℚ] c : ℚ_[ℓ] ⊗[ℚ] E) := by
  have h1 : IsIntegral ℤ ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] c : ℚ_[ℓ] ⊗[ℚ] E) :=
    map_isIntegral_int (Algebra.TensorProduct.includeRight (R := ℚ) (A := ℚ_[ℓ]) (B := E)) hc
  have h2 : IsIntegral ℤ_[ℓ] ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] c : ℚ_[ℓ] ⊗[ℚ] E) := by
    obtain ⟨P, hP, hP'⟩ := h1
    refine ⟨P.map (Int.castRingHom _), hP.map _, ?_⟩
    rw [Polynomial.eval₂_map, ← hP']
    congr 1
  let v : ℤ_[ℓ] := ⟨u, hu⟩
  have h3 := h2.smul v
  have e : v • ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] c : ℚ_[ℓ] ⊗[ℚ] E) = u ⊗ₜ[ℚ] c := by
    rw [TensorProduct.smul_tmul']
    congr 1
    change u * 1 = u
    exact mul_one u
  rwa [e] at h3

theorem exists_tmul_integral [FiniteDimensional ℚ E] (a : ℚ_[ℓ]) (c : E) :
    ∃ (a' : ℚ_[ℓ]) (c' : E), IsIntegral ℤ c' ∧ (a ⊗ₜ[ℚ] c : ℚ_[ℓ] ⊗[ℚ] E) = a' ⊗ₜ[ℚ] c' := by
  have hq : IsAlgebraic ℚ c := Algebra.IsAlgebraic.isAlgebraic c
  have hz : IsAlgebraic ℤ c := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 hq
  obtain ⟨m, hm, hi⟩ := hz.exists_integral_multiple
  refine ⟨((m : ℚ)⁻¹) • a, m • c, hi, ?_⟩
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  rw [TensorProduct.smul_tmul, ← Int.cast_smul_eq_zsmul ℚ, smul_smul, inv_mul_cancel₀ hm', one_smul]

theorem pow_mul_tmul (N : ℕ) (a : ℚ_[ℓ]) (c : E) :
    (ℓ : ℚ_[ℓ] ⊗[ℚ] E) ^ N * (a ⊗ₜ[ℚ] c) = ((ℓ : ℚ_[ℓ]) ^ N * a) ⊗ₜ[ℚ] c := by
  have : (ℓ : ℚ_[ℓ] ⊗[ℚ] E) ^ N = ((ℓ : ℚ_[ℓ]) ^ N) ⊗ₜ[ℚ] (1 : E) := by
    rw [← Nat.cast_pow, ← Nat.cast_pow, Algebra.TensorProduct.natCast_def]
  rw [this, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem exists_pow_mul_isIntegral [FiniteDimensional ℚ E] (x : ℚ_[ℓ] ⊗[ℚ] E) :
    ∃ N : ℕ, IsIntegral ℤ_[ℓ] ((ℓ : ℚ_[ℓ] ⊗[ℚ] E) ^ N * x) := by
  have hl : IsIntegral ℤ_[ℓ] (ℓ : ℚ_[ℓ] ⊗[ℚ] E) := by
    have := isIntegral_algebraMap (R := ℤ_[ℓ]) (A := ℚ_[ℓ] ⊗[ℚ] E) (x := (ℓ : ℤ_[ℓ]))
    rwa [map_natCast] at this
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [mul_zero]; exact isIntegral_zero⟩
  | add x y hx hy =>
    obtain ⟨M, hM⟩ := hx
    obtain ⟨N, hN⟩ := hy
    refine ⟨M + N, ?_⟩
    have := ((hl.pow N).mul hM).add ((hl.pow M).mul hN)
    have e : (ℓ : ℚ_[ℓ] ⊗[ℚ] E) ^ (M + N) * (x + y) = (ℓ : ℚ_[ℓ] ⊗[ℚ] E) ^ N * ((ℓ : ℚ_[ℓ] ⊗[ℚ] E) ^ M * x) +
        (ℓ : ℚ_[ℓ] ⊗[ℚ] E) ^ M * ((ℓ : ℚ_[ℓ] ⊗[ℚ] E) ^ N * y) := by ring
    rwa [e]
  | tmul a c =>
    obtain ⟨a', c', hc, e⟩ := exists_tmul_integral a c
    have hp : (1 : ℝ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).one_lt
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt ‖a'‖ hp
    refine ⟨N, ?_⟩
    rw [e, pow_mul_tmul]
    refine isIntegral_tmul _ ?_ _ hc
    rw [norm_mul, norm_pow, Padic.norm_p, inv_pow, inv_mul_le_iff₀ (by positivity), mul_one]
    exact hN.le

theorem exists_sub_eq_pow_mul [FiniteDimensional ℚ E] (N : ℕ) (x : ℚ_[ℓ] ⊗[ℚ] E) :
    ∃ (b : E) (t : ℚ_[ℓ] ⊗[ℚ] E), IsIntegral ℤ_[ℓ] t ∧
      (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b = x + (ℓ : ℚ_[ℓ] ⊗[ℚ] E) ^ N * t := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, isIntegral_zero, by simp⟩
  | add x y hx hy =>
    obtain ⟨b, t, ht, e⟩ := hx
    obtain ⟨b', t', ht', e'⟩ := hy
    refine ⟨b + b', t + t', ht.add ht', ?_⟩
    rw [TensorProduct.tmul_add, e, e']
    ring
  | tmul a c =>
    obtain ⟨a', c', hc, e⟩ := exists_tmul_integral a c
    have hp : (0 : ℝ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).pos
    have hl : (ℓ : ℚ_[ℓ]) ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
    obtain ⟨q, hq⟩ := Padic.rat_dense ℓ a' (ε := ((ℓ : ℝ) ^ N)⁻¹) (by positivity)
    refine ⟨q • c', (((q : ℚ_[ℓ]) - a') / (ℓ : ℚ_[ℓ]) ^ N) ⊗ₜ[ℚ] c', isIntegral_tmul _ ?_ _ hc, ?_⟩
    · rw [norm_div, norm_pow, Padic.norm_p, inv_pow, div_le_one (by positivity), norm_sub_rev]
      exact hq.le
    · rw [e, pow_mul_tmul, ← TensorProduct.add_tmul, ← TensorProduct.smul_tmul]
      congr 1
      rw [Rat.smul_one_eq_cast]
      field_simp
      ring

theorem exists_approx_unit (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E]
    (ℓ : ℕ) [Fact ℓ.Prime] (z : (ℚ_[ℓ] ⊗[ℚ] E)ˣ) :
    ∃ (b : E) (s : ℚ_[ℓ] ⊗[ℚ] E), IsIntegral ℤ_[ℓ] s ∧
      (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b = (z : ℚ_[ℓ] ⊗[ℚ] E) * (1 + (ℓ : ℚ_[ℓ] ⊗[ℚ] E) * s) := by
  obtain ⟨N, hN⟩ := exists_pow_mul_isIntegral ((z⁻¹ : (ℚ_[ℓ] ⊗[ℚ] E)ˣ) : ℚ_[ℓ] ⊗[ℚ] E)
  obtain ⟨b, t, ht, e⟩ := exists_sub_eq_pow_mul (N + 1) (z : ℚ_[ℓ] ⊗[ℚ] E)
  refine ⟨b, _, hN.mul ht, ?_⟩
  have h := z.mul_inv
  rw [e]
  linear_combination (-((ℓ : ℚ_[ℓ] ⊗[ℚ] E) ^ (N + 1) * t)) * h

end GlobalTheory.PadicTensorApprox
