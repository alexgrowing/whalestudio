import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemStandardOpenCoordinateRingIffLocalizationCharStatement
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

namespace GlobalTheory.PD

open Polynomial

theorem isIntegral_of_le {k F K : Type} [Field k] [Field F] [Field K] [Algebra k F] [Algebra F K]
    {A A' : Subalgebra k F} (h : A ≤ A') {y : K} (hy : IsIntegral A y) : IsIntegral A' y := by
  obtain ⟨p, hm, he⟩ := hy
  refine ⟨p.map (Subalgebra.inclusion h), hm.map _, ?_⟩
  rw [eval₂_map]
  exact he

theorem rA_mono (k : Type) [Field k] {F : Type} [Field F] [Algebra k F] {d : ℕ} (x : Fin (d + 1) → F)
    {I J : Finset (Fin (d + 1))} (h : I ⊆ J) : rA k x I ≤ rA k x J := by
  apply Algebra.adjoin_mono
  rintro y ⟨i, hi, j, rfl⟩
  exact ⟨i, h hi, j, rfl⟩

theorem rB_mono_loc : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K]
    [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x →
    ∀ (I : Finset (Fin (d + 1))) (i : Fin (d + 1)), i ∈ I →
    (∀ J, I ⊆ J → rB k K x I ≤ rB k K x J) ∧
    ∀ y : K, y ∈ rB k K x I ↔ ∃ N : ℕ, y * algebraMap F K (∏ j ∈ I, x j / x i) ^ N ∈ rB k K x {i} := by
  intro k _ _ F K _ _ _ _ _ _ d x hK I i hi
  have memB : ∀ (J : Finset (Fin (d + 1))) (y : K), y ∈ rB k K x J ↔ IsIntegral (rA k x J) y := fun J y => by
    rw [rB, Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
  refine ⟨fun J hJ y hy => (memB J y).2 (isIntegral_of_le (rA_mono k x hJ) ((memB I y).1 hy)), fun y => ?_⟩
  set s : F := ∏ j ∈ I, x j / x i with hs
  have hsi : s ∈ rA k x {i} := Subalgebra.prod_mem _ fun j _ =>
    Algebra.subset_adjoin ⟨i, Finset.mem_singleton_self i, j, rfl⟩
  have hsinv : s⁻¹ ∈ rA k x I := by
    rw [hs, ← Finset.prod_inv_distrib]
    refine Subalgebra.prod_mem _ fun j hj => ?_
    rw [inv_div]
    exact Algebra.subset_adjoin ⟨j, hj, i, rfl⟩
  have hsne : s ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => div_ne_zero (hK.pd.ne j) (hK.pd.ne i)
  have hiI : rA k x {i} ≤ rA k x I := rA_mono k x (Finset.singleton_subset_iff.2 hi)
  simp only [memB]
  constructor
  · rintro ⟨p, hm, he⟩
    have hc : ∀ m, ∃ N : ℕ, (p.coeff m : F) * s ^ N ∈ rA k x {i} := fun m =>
      (GlobalTheory.T.mem_standardOpenCoordinateRing_iff_localization_chart k F d x hK.pd I i hi (p.coeff m : F)).1 (p.coeff m).2
    choose Nf hNf using hc
    set N := (Finset.range (p.natDegree + 1)).sup Nf
    have hcN : ∀ m, (p.coeff m : F) * s ^ N ∈ rA k x {i} := by
      intro m
      by_cases hmd : m ≤ p.natDegree
      · have hle : Nf m ≤ N := Finset.le_sup (f := Nf) (Finset.mem_range.2 (Nat.lt_succ_of_le hmd))
        rw [← Nat.add_sub_cancel' hle, pow_add, ← mul_assoc]
        exact Subalgebra.mul_mem _ (hNf m) (Subalgebra.pow_mem _ hsi _)
      · rw [coeff_eq_zero_of_natDegree_lt (not_le.1 hmd)]
        simp
    set q : F[X] := (p.map (algebraMap (rA k x I) F)).scaleRoots (s ^ N)
    have hqm : q.Monic := (monic_scaleRoots_iff _).2 (hm.map _)
    have hdeg : (p.map (algebraMap (rA k x I) F)).natDegree = p.natDegree :=
      natDegree_map_eq_of_injective (fun a b h => Subtype.ext h) _
    have hl : q ∈ lifts (algebraMap (rA k x {i}) F) := by
      rw [lifts_iff_coeff_lifts]
      intro m
      rw [coeff_scaleRoots, coeff_map, hdeg]
      have hmem : (algebraMap (rA k x I) F (p.coeff m)) * (s ^ N) ^ (p.natDegree - m) ∈ rA k x {i} := by
        by_cases hmd : m < p.natDegree
        · obtain ⟨e, he'⟩ : ∃ e, p.natDegree - m = e + 1 := ⟨p.natDegree - m - 1, by omega⟩
          rw [he', pow_succ', ← mul_assoc]
          exact Subalgebra.mul_mem _ (hcN m) (Subalgebra.pow_mem _ (Subalgebra.pow_mem _ hsi _) _)
        · rw [Nat.sub_eq_zero_of_le (not_lt.1 hmd), pow_zero, mul_one]
          rcases (not_lt.1 hmd).eq_or_lt with h | h
          · rw [← h, hm.coeff_natDegree, map_one]
            exact Subalgebra.one_mem _
          · rw [coeff_eq_zero_of_natDegree_lt h, map_zero]
            exact Subalgebra.zero_mem _
      exact ⟨⟨_, hmem⟩, rfl⟩
    obtain ⟨q0, hq0, -, hq0m⟩ := lifts_and_natDegree_eq_and_monic hl hqm
    refine ⟨N, q0, hq0m, ?_⟩
    have h1 : eval₂ (algebraMap F K) y (p.map (algebraMap (rA k x I) F)) = 0 := by
      rw [eval₂_map]
      exact he
    have h2 : eval₂ (algebraMap F K) (algebraMap F K (s ^ N) * y) q = 0 :=
      scaleRoots_eval₂_eq_zero (algebraMap F K) (s := s ^ N) h1
    rw [← map_pow, mul_comm]
    rw [← hq0, eval₂_map] at h2
    exact h2
  · rintro ⟨N, hN⟩
    have h1 : IsIntegral (rA k x I) (y * algebraMap F K s ^ N) := isIntegral_of_le hiI hN
    have h2 : IsIntegral (rA k x I) (algebraMap F K s⁻¹ ^ N) := by
      have : IsIntegral (rA k x I) (algebraMap (rA k x I) K ⟨s⁻¹, hsinv⟩) := isIntegral_algebraMap
      exact this.pow N
    have h3 := h1.mul h2
    rwa [mul_assoc, ← mul_pow, ← map_mul, mul_inv_cancel₀ hsne, map_one, one_pow, mul_one] at h3

end GlobalTheory.PD
