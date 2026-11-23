import Mathlib
import Formalism.SatakeDualWeyl.Statement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMatLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyEqPowOfIrreducible

noncomputable section

open Polynomial Matrix GlobalTheory.LatOrb IsLocalRing

namespace GlobalTheory.MaxOrder

theorem exists_eq_uniformizer_smul {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field K] [Algebra O K] [IsFractionRing O K] {n : ℕ} (P₀ : O[X])
    (hP : IsCoprime P₀ (derivative P₀)) (γ : Matrix (Fin n) (Fin n) K)
    (hγ : γ.charpoly = P₀.map (algebraMap O K)) (π : O) (hπ : Irreducible π)
    (y : Matrix (Fin n) (Fin n) K) (hy : IsIntegral O y) (N : ℕ) (hN : 1 ≤ N) (f : O[X])
    (hf : aeval γ f = π ^ N • y) : ∃ h : O[X], aeval γ f = π • aeval γ h := by
  classical
  obtain ⟨Q, hQm, hQ⟩ := hy
  set m := Q.natDegree with hm
  set u := π ^ N with hu
  let F : O[X] := ∑ i ∈ Finset.range (m + 1), C (Q.coeff i * u ^ (m - i)) * f ^ i
  have hF : aeval γ F = 0 := by
    have h1 : aeval γ F = u ^ m • aeval y Q := by
      rw [aeval_eq_sum_range (p := Q) y, Finset.smul_sum]
      simp only [F, map_sum, map_mul, aeval_C, map_pow, hf]
      refine Finset.sum_congr rfl fun i hi => ?_
      have him : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      have hAlg : ∀ (c : O) (X : Matrix (Fin n) (Fin n) K), algebraMap O _ c * X = c • X :=
        fun c X => (Algebra.smul_def c X).symm
      have hmi : u ^ (m - i) * u ^ i = u ^ m := by rw [← pow_add, Nat.sub_add_cancel him]
      simp only [_root_.smul_pow, ← map_pow, hAlg, smul_mul_assoc, smul_smul]
      congr 1
      linear_combination (Q.coeff i) * hmi
    rw [h1, show aeval y Q = 0 from hQ, smul_zero]
  have hmon : P₀.Monic := monic_of_injective (IsFractionRing.injective O K) (hγ ▸ γ.charpoly_monic)
  have hd : P₀ ∣ F ^ n := by
    have h := GlobalTheory.CharpolyPowIrred.charpoly_dvd_pow_of_aeval γ (F.map (algebraMap O K))
      (by rw [aeval_map_algebraMap]; exact hF)
    rw [hγ, Fintype.card_fin, ← Polynomial.map_pow] at h
    exact (map_dvd_map _ (IsFractionRing.injective O K) hmon).1 h
  let φ := residue O
  have hφπ : φ π = 0 := (residue_eq_zero_iff π).2 ((mem_maximalIdeal _).2 hπ.not_isUnit)
  have hFm : F.map φ = (f.map φ) ^ m := by
    simp only [F, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow, map_C, map_mul, map_pow]
    rw [Finset.sum_range_succ, Finset.sum_eq_zero, zero_add, hQm.coeff_natDegree, Nat.sub_self,
      pow_zero, mul_one, map_one, C_1, one_mul]
    intro i hi
    have him : 0 < m - i := Nat.sub_pos_of_lt (Finset.mem_range.1 hi)
    rw [hu, map_pow, hφπ, zero_pow (by omega), C_0, zero_pow him.ne', mul_zero, zero_mul]
  have hsep : (P₀.map φ).Separable := by
    unfold Separable
    rw [derivative_map]
    exact hP.map (mapRingHom φ)
  have hd2 : P₀.map φ ∣ (f.map φ) ^ (m * n + 1) := by
    have h := Polynomial.map_dvd φ hd
    rw [Polynomial.map_pow, hFm, ← pow_mul] at h
    exact h.trans (pow_dvd_pow _ (Nat.le_succ _))
  obtain ⟨qb, hqb⟩ := (hsep.squarefree.dvd_pow_iff_dvd (Nat.succ_ne_zero _)).1 hd2
  obtain ⟨q, rfl⟩ := Polynomial.map_surjective φ (residue_surjective) qb
  have hker : f - P₀ * q ∈ Ideal.span {C π} := by
    have h : f - P₀ * q ∈ RingHom.ker (mapRingHom φ) := by
      rw [RingHom.mem_ker, coe_mapRingHom, Polynomial.map_sub, Polynomial.map_mul, hqb, sub_self]
    rwa [Polynomial.ker_mapRingHom, ker_residue, (IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ,
      Ideal.map_span, Set.image_singleton] at h
  obtain ⟨h, hh⟩ := Ideal.mem_span_singleton'.1 hker
  refine ⟨h, ?_⟩
  have hP0 : aeval γ P₀ = 0 := by
    rw [← aeval_map_algebraMap K, ← hγ, aeval_self_charpoly]
  have hfe : f = P₀ * q + h * C π := by rw [hh]; ring
  rw [hfe, map_add, map_mul, map_mul, hP0, zero_mul, zero_add, aeval_C, ← Algebra.commutes,
    ← Algebra.smul_def]

theorem isIntegral_aeval_eq_aeval_map : ∀ {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] (n : ℕ) (P₀ : O[X]), IsCoprime P₀ (derivative P₀) →
    ∀ γ : Matrix (Fin n) (Fin n) K, γ.charpoly = P₀.map (algebraMap O K) →
    ∀ p : K[X], IsIntegral O (aeval γ p) → ∃ r : O[X], aeval γ p = aeval γ (r.map (algebraMap O K)) := by
  intro O K _ _ _ _ _ _ n P₀ hP γ hγ p hp
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  simp only [aeval_map_algebraMap]
  have hπK : algebraMap O K π ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective O K)]; exact hπ.ne_zero
  have key : ∀ k : ℕ, ∀ f : O[X], aeval γ f = π ^ k • aeval γ p → ∃ r : O[X], aeval γ p = aeval γ r := by
    intro k
    induction k with
    | zero => intro f hf; exact ⟨f, by rw [hf, pow_zero, one_smul]⟩
    | succ k ih =>
      intro f hf
      obtain ⟨h, hh⟩ := exists_eq_uniformizer_smul P₀ hP γ hγ π hπ _ hp (k + 1) (by omega) f hf
      refine ih h ?_
      have h1 : π • (π ^ k • aeval γ p) = π • aeval γ h := by rw [smul_smul, ← pow_succ', ← hf, hh]
      rw [← algebraMap_smul K π (π ^ k • aeval γ p), ← algebraMap_smul K π (aeval γ h)] at h1
      exact (smul_right_injective _ hπK h1).symm
  obtain ⟨b, hb⟩ := IsLocalization.integerNormalization_map_to_map (nonZeroDivisors O) p
  obtain ⟨k, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero b.2) hπ
  refine key k (C (↑v⁻¹ : O) * IsLocalization.integerNormalization (nonZeroDivisors O) p) ?_
  rw [map_mul, aeval_C, ← aeval_map_algebraMap K γ (IsLocalization.integerNormalization _ p), hb,
    ← algebraMap_smul K (b : O) p, map_smul, algebraMap_smul, ← Algebra.smul_def, smul_smul, hv,
    ← mul_assoc, Units.inv_mul, one_mul]

end GlobalTheory.MaxOrder
