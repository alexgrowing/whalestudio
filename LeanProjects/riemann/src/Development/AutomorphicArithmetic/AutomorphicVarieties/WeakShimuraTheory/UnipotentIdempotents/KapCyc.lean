import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.TCont

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private theorem torsion_combination_smul_eq_zero {M : Type} [AddCommGroup M] (x γ β ε ω : M) (m n k q r : ℕ) (j : ℤ)
    (hx : m • x = 0) (hω : n • ω = 0) (hγ : 2 • γ + ω = ε) (hβ : k • (2 • β + (-(2 * j + 1)) • ε) = 0) :
    (2 * k * m * n) • (x + (2 * q + r + 4) • (-γ) + r • β + (-(r * j - q - 2 : ℤ)) • ε) = 0 := by
  linear_combination (norm := module) (2 * k * n : ℤ) • hx + (k * m * (2 * q + r + 4) : ℤ) • hω - (k * m * n * (2 * q + r + 4) : ℤ) • hγ + (m * n * r : ℤ) • hβ

private theorem mul_aux {M : Type} [CommGroup M] (x γ β ε ω : M) (m n k q r : ℕ) (j : ℤ)
    (hx : x ^ m = 1) (hω : ω ^ n = 1) (hγ : γ ^ 2 * ω = ε) (hβ : (β ^ 2 * ε ^ (-(2 * j + 1))) ^ k = 1) :
    (x * γ⁻¹ ^ (2 * q + r + 4) * β ^ r * ε ^ (-(r * j - q - 2 : ℤ))) ^ (2 * k * m * n) = 1 := by
  have h := torsion_combination_smul_eq_zero (M := Additive M) (Additive.ofMul x) (Additive.ofMul γ) (Additive.ofMul β)
    (Additive.ofMul ε) (Additive.ofMul ω) m n k q r j
    (by rw [← ofMul_pow, hx, ofMul_one]) (by rw [← ofMul_pow, hω, ofMul_one])
    (by rw [← ofMul_pow, ← ofMul_mul, hγ])
    (by rw [← ofMul_zpow, ← ofMul_pow, ← ofMul_mul, ← ofMul_pow, hβ, ofMul_one])
  apply_fun Additive.toMul at h
  simpa [toMul_nsmul, toMul_zsmul, toMul_add, toMul_neg, mul_pow, inv_pow] using h

theorem UpperTheory.V.Ws.Lk.kapCyc :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} (P : Pre T), D.Good → ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ (a b : ℤ) (k : ℕ), 0 < k ∧ Odd b ∧ ∀ g ∈ Ine (F := T.L) A, (P.κ g * cycBar T.L Ω l g ^ (-a)) ^ k = 1 ∧ (P.βL g ^ 2 * cycBar T.L Ω l g ^ (-b)) ^ k = 1 := by
  intro Ω _ _ _ l _ c D T P hG A hA
  obtain ⟨b, k, hk, hb, hcyc⟩ := P.cyc A hA
  obtain ⟨j, rfl⟩ := hb
  obtain ⟨m, hm, hm1⟩ := P.κ₀_ord
  have hl : l.Prime := Fact.out
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      exact absurd (Nat.coprime_zero_right l |>.1 hm) hl.one_lt.ne'
    · exact h
  have hn0 : 0 < l - 1 := Nat.sub_pos_of_lt hl.one_lt
  refine ⟨((D.e % 2 : ℕ) : ℤ) * j - ((D.e / 2 : ℕ) : ℤ) - 2, 2 * j + 1, 2 * k * m * (l - 1),
    by positivity, ⟨j, rfl⟩, ?_⟩
  intro g hg
  have hω : (toQ D.om (resQ T.L g)) ^ (l - 1) = 1 := by
    rw [show toQ D.om (resQ T.L g) = Units.map (algebraMap c.O (PadicAlgCl l) : c.O →* PadicAlgCl l)
        (D.om (resQ T.L g)) from rfl,
      ← map_pow, ← MonoidHom.pow_apply, hG.om_pow, MonoidHom.one_apply, map_one]
  have hγ : P.γ (resQ T.L g) ^ 2 * toQ D.om (resQ T.L g) = cycBar T.L Ω l g := P.γ_sq _
  have hβ : (P.β (resLe (K_le T) g) ^ 2 * cycBar T.L Ω l g ^ (-(2 * j + 1))) ^ k = 1 :=
    hcyc _ hg
  have hx : P.κ₀ (resLe (K_le T) g) ^ m = 1 := by
    rw [← MonoidHom.pow_apply, hm1, MonoidHom.one_apply]
  have hκ : P.κ g = P.κ₀ (resLe (K_le T) g) * (P.γ (resQ T.L g))⁻¹ ^ (D.e + 4) *
      P.β (resLe (K_le T) g) ^ (D.e % 2) := rfl
  constructor
  · rw [hκ, show D.e + 4 = 2 * (D.e / 2) + D.e % 2 + 4 by omega]
    exact mul_aux _ _ _ _ _ m (l - 1) k (D.e / 2) (D.e % 2) j hx hω hγ hβ
  · show (P.β (resLe (K_le T) g) ^ 2 * cycBar T.L Ω l g ^ (-(2 * j + 1))) ^ (2 * k * m * (l - 1)) = 1
    rw [show 2 * k * m * (l - 1) = k * (2 * m * (l - 1)) by ring, pow_mul, hβ, one_pow]
