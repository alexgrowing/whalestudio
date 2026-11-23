import Mathlib

open Polynomial Matrix

private theorem UpperTheory.V.Pr.T.unipTorsion_unit {A : Type} [CommRing A] [IsLocalRing A] (χ : A[X]) (n m : ℕ)
    (hχ : χ.Monic) (hr : χ.map (IsLocalRing.residue A) = (X - 1) ^ n) (hm : IsUnit (m : A)) :
    IsUnit (AdjoinRoot.mk χ (∑ i ∈ Finset.range m, X ^ i)) := by
  haveI : Module.Finite A (AdjoinRoot χ) := (AdjoinRoot.powerBasis' hχ).finite
  haveI : Algebra.IsIntegral A (AdjoinRoot χ) := Algebra.IsIntegral.of_finite A _
  by_contra hnu
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ (mt Ideal.span_singleton_eq_top.mp hnu)
  have hmem : AdjoinRoot.mk χ (∑ i ∈ Finset.range m, X ^ i) ∈ M := hle (Ideal.mem_span_singleton_self _)
  letI : Field (AdjoinRoot χ ⧸ M) := Ideal.Quotient.field M
  set π : AdjoinRoot χ →+* AdjoinRoot χ ⧸ M := Ideal.Quotient.mk M with hπdef
  set φ : A →+* AdjoinRoot χ ⧸ M := π.comp (algebraMap A (AdjoinRoot χ)) with hφdef
  have hcomap : Ideal.comap (algebraMap A (AdjoinRoot χ)) M = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M)
  have hker : ∀ a ∈ IsLocalRing.maximalIdeal A, φ a = 0 := by
    intro a ha
    rw [← hcomap, Ideal.mem_comap] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
  set ψ : IsLocalRing.ResidueField A →+* AdjoinRoot χ ⧸ M := Ideal.Quotient.lift (IsLocalRing.maximalIdeal A) φ hker with hψdef
  have hψ : ψ.comp (IsLocalRing.residue A) = φ := by
    ext a
    exact Ideal.Quotient.lift_mk (IsLocalRing.maximalIdeal A) φ hker
  have key : ∀ p : A[X], π (AdjoinRoot.mk χ p) = eval₂ φ (π (AdjoinRoot.root χ)) p := by
    intro p
    rw [← AdjoinRoot.aeval_eq, aeval_def, hom_eval₂]
  have hroot : π (AdjoinRoot.root χ) = 1 := by
    have h0 := key χ
    rw [AdjoinRoot.mk_self, map_zero, ← hψ, ← eval₂_map, hr] at h0
    simp only [eval₂_pow, eval₂_sub, eval₂_X, eval₂_one] at h0
    exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero h0.symm)
  have hs := key (∑ i ∈ Finset.range m, X ^ i)
  have hz : π (AdjoinRoot.mk χ (∑ i ∈ Finset.range m, X ^ i)) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  rw [hz, hroot] at hs
  simp only [eval₂_finset_sum, eval₂_X_pow, one_pow, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one] at hs
  have hu := hm.map φ
  rw [map_natCast] at hu
  exact hu.ne_zero hs.symm

theorem UpperTheory.V.Pr.T.unipTorsion :
    ∀ {A E : Type} [CommRing A] [IsLocalRing A] [Ring E] [Algebra A E] (γ : E) (χ : A[X]) (n m : ℕ),
      χ.Monic → aeval γ χ = 0 → χ.map (IsLocalRing.residue A) = (X - 1) ^ n → IsUnit (m : A) → γ ^ m = 1 → γ = 1 := by
  intro A E _ _ _ _ γ χ n m hχ hγ hr hm hγm
  have hu := UpperTheory.V.Pr.T.unipTorsion_unit χ n m hχ hr hm
  obtain ⟨b, hb⟩ := hu.exists_right_inv
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective b
  rw [← map_mul, ← map_one (AdjoinRoot.mk χ), AdjoinRoot.mk_eq_mk] at hb
  obtain ⟨q, hq⟩ := hb
  have h1 : aeval γ (∑ i ∈ Finset.range m, (X : A[X]) ^ i) * aeval γ p = 1 := by
    rw [← map_mul, ← sub_eq_zero, ← map_one (aeval (R := A) γ), ← map_sub, hq, map_mul, hγ, zero_mul]
  have h2 : (1 - γ) * aeval γ (∑ i ∈ Finset.range m, (X : A[X]) ^ i) = 0 := by
    rw [map_sum]
    simp only [map_pow, aeval_X]
    rw [mul_neg_geom_sum, hγm, sub_self]
  have h3 : 1 - γ = 0 := by
    calc 1 - γ = (1 - γ) * (aeval γ (∑ i ∈ Finset.range m, (X : A[X]) ^ i) * aeval γ p) := by
          rw [h1, mul_one]
      _ = 0 := by rw [← mul_assoc, h2, zero_mul]
  exact (sub_eq_zero.mp h3).symm
