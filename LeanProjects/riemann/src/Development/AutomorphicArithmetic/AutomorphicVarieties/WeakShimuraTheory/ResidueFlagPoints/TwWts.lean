import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.ResLeCont

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.CuspRep GlobalTheory.GalOfCusp

private theorem aux {M : Type} [CommGroup M] (x y z : M) (a b : ℤ) (k n : ℕ) (h1 : (x * z ^ (-a)) ^ k = 1)
    (h2 : (y ^ 2 * z ^ (-b)) ^ k = 1) : ((x * y ^ n) ^ 2 * z ^ (-(2 * a + n * b))) ^ k = 1 := by
  have e : (x * y ^ n) ^ 2 * z ^ (-(2 * a + n * b)) = (x * z ^ (-a)) ^ 2 * (y ^ 2 * z ^ (-b)) ^ n := by
    simp only [mul_pow, ← zpow_natCast, ← zpow_mul, mul_zpow]
    rw [show -(2 * a + (n:ℤ) * b) = -a * 2 + -b * n by ring, zpow_add]
    push_cast
    rw [mul_comm (n:ℤ) 2]
    ac_rfl
  rw [e, mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 k, mul_comm n k, pow_mul, pow_mul, h1, h2, one_pow, one_pow,
    one_mul]

theorem UpperTheory.V.Ws.Pt.twWts :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (n : ℕ) (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 → ∃ (e : ℤ) (k : ℕ), 0 < k ∧ Even (e + n) ∧ ∀ g ∈ Ine (F := T.L) A, (K.twc n g ^ 2 * cycBar T.L Ω l g ^ (-e)) ^ k = 1 := by
  intro Ω _ _ _ l _ c D T c' h K n A hA
  obtain ⟨a, b, k, hk, hb, hg⟩ := K.cyc A hA
  refine ⟨2 * a + n * b, k, hk, ?_, fun g hgA => ?_⟩
  · obtain ⟨m, rfl⟩ := hb
    exact ⟨a + n * m + n, by ring⟩
  · obtain ⟨h1, h2⟩ := hg g hgA
    have hc : cycBar T.L Ω l g
        = Units.map (algebraMap c'.O (PadicAlgCl l) : c'.O →* PadicAlgCl l) (chiO T.L Ω l c'.O g) := by
      ext
      change algebraMap ℚ_[l] (PadicAlgCl l) (PadicInt.Coe.ringHom ((cycZ T.L Ω l g : ℤ_[l]ˣ) : ℤ_[l]))
        = algebraMap c'.O (PadicAlgCl l) (algebraMap ℤ_[l] c'.O ((cycZ T.L Ω l g : ℤ_[l]ˣ) : ℤ_[l]))
      rw [← IsScalarTower.algebraMap_apply ℤ_[l] c'.O (PadicAlgCl l),
        IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
      rfl
    have ht : K.twc n g
        = Units.map (algebraMap c'.O (PadicAlgCl l) : c'.O →* PadicAlgCl l) (K.κ g * K.β g ^ n) := rfl
    rw [hc, ht, ← map_pow, ← map_zpow, ← map_mul, ← map_pow, aux _ _ _ a b k n h1 h2, map_one]
