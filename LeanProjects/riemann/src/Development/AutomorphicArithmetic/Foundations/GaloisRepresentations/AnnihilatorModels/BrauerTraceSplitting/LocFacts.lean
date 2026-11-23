import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.LocFacts

open Formalism.Per6 in
private theorem exists_finset_adjoin_laurent_preimage {A : Type} [CommRing A] (a t c : A) (r : ℕ) (hc : t ^ r = a * c)
    (x : Loc2 a t) : ∃ (k : ℕ) (y : A), Loc2.mk₀ a t t ^ k * x = Loc2.mk₀ a t y := by
  obtain ⟨n, b, hb⟩ := IsLocalization.Away.surj
    (algebraMap A (Localization.Away a) t) (S := Localization.Away (algebraMap A (Localization.Away a) t)) x
  obtain ⟨m, y, hy⟩ := IsLocalization.Away.surj a (S := Localization.Away a) b
  have hb' : x * Loc2.mk₀ a t t ^ n = Loc2.mk₁ a t b := hb
  have hy' : Loc2.mk₁ a t b * Loc2.mk₀ a t a ^ m = Loc2.mk₀ a t y := by
    have := congrArg (Loc2.mk₁ a t) hy
    simpa [Loc2.mk₀] using this
  refine ⟨r * m + n, y * c ^ m, ?_⟩
  have hT : Loc2.mk₀ a t t ^ r = Loc2.mk₀ a t a * Loc2.mk₀ a t c := by
    rw [← map_pow, hc, map_mul]
  rw [map_mul, map_pow, ← hy', ← hb', pow_add, pow_mul, hT, mul_pow]
  ring

open Formalism.Per6 in
private theorem exists_pow_kill_of_localization_zero {A : Type} [CommRing A] (a t c : A) (r : ℕ) (hc : t ^ r = a * c)
    (y : A) (hy : Loc2.mk₀ a t y = 0) : ∃ k : ℕ, t ^ k * y = 0 := by
  have h1 : algebraMap (Localization.Away a) (Localization.Away (algebraMap A (Localization.Away a) t))
      (algebraMap A (Localization.Away a) y) = 0 := hy
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff
    (Submonoid.powers (algebraMap A (Localization.Away a) t)) _ _).1 h1
  have h2 : algebraMap A (Localization.Away a) (t ^ k * y) = 0 := by
    simpa [map_mul, map_pow] using hk
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers a) _ _).1 h2
  refine ⟨r * m + k, ?_⟩
  have hm' : a ^ m * (t ^ k * y) = 0 := hm
  calc t ^ (r * m + k) * y = c ^ m * (a ^ m * (t ^ k * y)) := by
        rw [pow_add, pow_mul, hc, mul_pow]; ring
    _ = 0 := by rw [hm', mul_zero]

theorem UpperTheory.Gal.crystallineComparison.Br.locFacts :
    UpperTheory.Gal.crystallineComparison.Br.LocFacts := by
  intro A _ a t ⟨r, c, hc⟩
  exact ⟨exists_finset_adjoin_laurent_preimage a t c r hc, exists_pow_kill_of_localization_zero a t c r hc⟩
