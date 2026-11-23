import Mathlib

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

private theorem idempotent_mul_eval₂_mul_eq {A B : Type} [CommRing A] [CommRing B] (a : A →+* B) (e b : B)
    (he : IsIdempotentElem e) (p : Polynomial A) :
    e * p.eval₂ a (e * b) = e * p.eval₂ a b := by
  rw [Polynomial.eval₂_eq_sum_range, Polynomial.eval₂_eq_sum_range, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h := he.pow_succ_eq i
  rw [mul_pow]
  linear_combination (a (p.coeff i) * b ^ i) * h

theorem UpperTheory.integralClosure_range_isLocalization_idempotent :
    ∀ {A B B' C C' : Type} [CommRing A] [CommRing B] [CommRing B'] [CommRing C] [CommRing C']
        (a : A →+* B) (jB : B →+* B') (t : C →+* B) (t' : C' →+* B') (mC : C →+* C'),
        Function.Injective t → Function.Injective t' →
        (∀ b, b ∈ t.range ↔ a.IsIntegralElem b) →
        (∀ b, b ∈ t'.range ↔ (jB.comp a).IsIntegralElem b) →
        (∀ c, jB (t c) = t' (mC c)) →
        ∀ (S : Submonoid B), (∀ s ∈ S, IsIdempotentElem s) →
        @IsLocalization B _ S B' _ jB.toAlgebra →
        mC.Flat ∧ Epi (CommRingCat.ofHom mC) := by
  intro A B B' C C' _ _ _ _ _ a jB t t' mC ht ht' hC hC' hcomm S hS hloc
  letI := jB.toAlgebra
  have h1 : ∀ s ∈ S, jB s = 1 := by
    intro s hs
    have hu : IsUnit (jB s) := IsLocalization.map_units B' (⟨s, hs⟩ : S)
    have hid : jB s * jB s = jB s * 1 := by rw [← map_mul, (hS s hs).eq, mul_one]
    exact hu.mul_left_cancel hid
  have hint : ∀ s ∈ S, s ∈ t.range := by
    intro s hs
    rw [hC]
    refine ⟨Polynomial.X * (Polynomial.X - Polynomial.C 1),
      Polynomial.monic_X.mul (Polynomial.monic_X_sub_C 1), ?_⟩
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_sub, Polynomial.eval₂_X,
      Polynomial.eval₂_C, map_one, mul_sub, mul_one, (hS s hs).eq, sub_self]
  have hsurj : Function.Surjective mC := by
    intro z
    obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalization.surj S (t' z)
    have hbs' : t' z = jB b := by
      have h : t' z * jB s = jB b := hbs
      rw [h1 _ s.2, mul_one] at h
      exact h
    obtain ⟨p, hp, hpz⟩ := (hC' (t' z)).mp ⟨z, rfl⟩
    have hj : jB (Polynomial.eval₂ a b p) = jB 0 := by
      rw [map_zero, Polynomial.hom_eval₂, ← hbs']
      exact hpz
    obtain ⟨⟨s', hs'⟩, hs'e⟩ := (IsLocalization.eq_iff_exists S B').mp hj
    have hs'0 : s' * Polynomial.eval₂ a b p = 0 := by simpa using hs'e
    have hsb : s' * b ∈ t.range := by
      rw [hC]
      refine ⟨Polynomial.X * p, Polynomial.monic_X.mul hp, ?_⟩
      rw [Polynomial.eval₂_mul, Polynomial.eval₂_X]
      calc s' * b * Polynomial.eval₂ a (s' * b) p
          = b * (s' * Polynomial.eval₂ a (s' * b) p) := by ring
        _ = b * (s' * Polynomial.eval₂ a b p) := by rw [idempotent_mul_eval₂_mul_eq a s' b (hS s' hs') p]
        _ = 0 := by rw [hs'0, mul_zero]
    obtain ⟨c0, hc0⟩ := hsb
    refine ⟨c0, ht' ?_⟩
    rw [← hcomm, hc0, map_mul, h1 _ hs', one_mul, hbs']
  letI := mC.toAlgebra
  have hloc' : IsLocalization (S.comap t) C' := by
    rw [isLocalization_iff]
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨c, hc⟩
      have : mC c = 1 := ht' (by rw [← hcomm, map_one]; exact h1 _ hc)
      show IsUnit (mC c)
      rw [this]
      exact isUnit_one
    · intro z
      obtain ⟨c, rfl⟩ := hsurj z
      refine ⟨(c, 1), ?_⟩
      show mC c * mC ((1 : S.comap t) : C) = mC c
      simp
    · intro x y hxy
      have hj : jB (t x) = jB (t y) := by
        rw [hcomm, hcomm]
        exact congrArg t' hxy
      obtain ⟨⟨s, hs⟩, e⟩ := (IsLocalization.eq_iff_exists S B').mp hj
      obtain ⟨cs, hcs⟩ := hint s hs
      refine ⟨⟨cs, show t cs ∈ S by rw [hcs]; exact hs⟩, ht ?_⟩
      simp only [map_mul]
      rw [hcs]
      exact e
  exact ⟨IsLocalization.flat C' (S.comap t), ConcreteCategory.epi_of_surjective _ hsurj⟩
