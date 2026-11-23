import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ContinuousResLe
import Mathlib.RingTheory.Polynomial.Resultant.Basic

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem coprime_of_residue {B : Type} [CommRing B] [IsLocalRing B] (p q : B[X]) (hp : p.Monic)
    (h : IsCoprime (p.map (residue B)) (q.map (residue B))) : IsCoprime p q := by
  rw [← isUnit_resultant_iff_isCoprime hp]
  have hp' : (p.map (residue B)).Monic := hp.map _
  have h1 := (isUnit_resultant_iff_isCoprime hp').2 h
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le (natDegree_map_le (f := residue B) (p := q))
  have h2 : residue B (p.resultant q) = (p.map (residue B)).resultant (q.map (residue B)) := by
    rw [← resultant_map_map, hj, resultant_add_right_deg _ _ _ _ _ le_rfl,
      ← hp.natDegree_map (residue B), hp'.coeff_natDegree, one_pow, one_mul]
  rw [← h2] at h1
  exact (isUnit_map_iff (residue B) _).1 h1

theorem UpperTheory.V.Ws.phiRigid :
    ∀ {B E k : Type} [CommRing B] [IsLocalRing B] [Ring E] [Algebra B E] [Field k] (f : B →+* k), (∀ x, f x = 0 → x ∈ maximalIdeal B) → ∀ (M : E) (p : B[X]) (d m : ℕ), p.Monic → aeval M p = 0 → p.map f = (Polynomial.X - 1) ^ d → M ^ m = 1 → IsUnit (m : B) → M = 1 := by
  intro B E k _ _ _ _ _ f hf M p d m hp hM hpf hm hu
  have h1 : p.map (residue B) = (Polynomial.X - 1) ^ d := by
    have h0 : (p - (Polynomial.X - 1) ^ d).map f = 0 := by
      simp [Polynomial.map_sub, Polynomial.map_pow, hpf]
    have h2 : (p - (Polynomial.X - 1) ^ d).map (residue B) = 0 := by
      ext i
      rw [coeff_map, coeff_zero, residue_eq_zero_iff]
      apply hf
      rw [← coeff_map, h0, coeff_zero]
    simpa [Polynomial.map_sub, Polynomial.map_pow, sub_eq_zero] using h2
  set S : B[X] := ∑ i ∈ Finset.range m, Polynomial.X ^ i with hS
  have hc : IsCoprime p S := by
    apply coprime_of_residue p S hp
    rw [h1]
    apply IsCoprime.pow_left
    have hirr : Irreducible (Polynomial.X - C (1 : ResidueField B)) := irreducible_X_sub_C 1
    rw [← C_1, hirr.coprime_iff_not_dvd, dvd_iff_isRoot]
    have h3 : ((m : ℕ) : ResidueField B) ≠ 0 := by
      have := (hu.map (residue B)).ne_zero
      rwa [map_natCast] at this
    simpa [hS, Polynomial.map_sum, eval_finset_sum] using h3
  obtain ⟨a, b, hab⟩ := hc
  have h4 : aeval M b * aeval M S = 1 := by
    have := congrArg (aeval M) hab
    simpa [hM] using this
  have h5 : aeval M S * (M - 1) = 0 := by
    have : aeval M S = ∑ i ∈ Finset.range m, M ^ i := by simp [hS]
    rw [this, geom_sum_mul, hm, sub_self]
  have h6 : M - 1 = 0 := by
    have := congrArg (aeval M b * ·) h5
    simpa only [← mul_assoc, h4, one_mul, mul_zero] using this
  exact sub_eq_zero.1 h6
