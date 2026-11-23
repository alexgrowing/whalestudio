import Mathlib

open scoped TensorProduct

namespace GlobalTheory

theorem valuationRing_exists_dvd_all {O ι : Type} [CommRing O] [IsDomain O] [ValuationRing O]
    (f : ι → O) (s : Finset ι) (hs : s.Nonempty) : ∃ i ∈ s, ∀ j ∈ s, f i ∣ f j := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => exact ⟨a, by simp, by simp⟩
  | cons a s ha hs ih =>
    obtain ⟨i, hi, h⟩ := ih
    rcases ValuationRing.dvd_total (f a) (f i) with h1 | h1
    · refine ⟨a, by simp, fun j hj => ?_⟩
      rcases Finset.mem_cons.1 hj with rfl | hj
      · exact dvd_rfl
      · exact h1.trans (h j hj)
    · refine ⟨i, by simp [hi], fun j hj => ?_⟩
      rcases Finset.mem_cons.1 hj with rfl | hj
      · exact h1
      · exact h j hj

theorem mvPolynomial_map_maximalIdeal_isPrime (O : Type) [CommRing O] [IsLocalRing O] (g : ℕ) :
    ((IsLocalRing.maximalIdeal O).map (MvPolynomial.C : O →+* MvPolynomial (Fin g) O)).IsPrime := by
  have h : (IsLocalRing.maximalIdeal O).map (MvPolynomial.C : O →+* MvPolynomial (Fin g) O)
      = RingHom.ker (MvPolynomial.map (σ := Fin g) (IsLocalRing.residue O)) := by
    ext F
    rw [MvPolynomial.mem_map_C_iff, RingHom.mem_ker, MvPolynomial.ext_iff]
    simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_zero, IsLocalRing.residue_eq_zero_iff]
  rw [h]
  exact RingHom.ker_isPrime _

theorem mvPolynomial_exists_content (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] (g : ℕ)
    (F : MvPolynomial (Fin g) O) (hF : F ≠ 0) :
    ∃ (π : O) (F' : MvPolynomial (Fin g) O), F = MvPolynomial.C π * F' ∧
      F' ∉ (IsLocalRing.maximalIdeal O).map (MvPolynomial.C : O →+* MvPolynomial (Fin g) O) := by
  obtain ⟨i, hi, h⟩ := valuationRing_exists_dvd_all (fun m => F.coeff m) F.support
    (MvPolynomial.support_nonempty.2 hF)
  have hd : MvPolynomial.C (F.coeff i) ∣ F := by
    rw [MvPolynomial.C_dvd_iff_dvd_coeff]
    intro m
    by_cases hm : m ∈ F.support
    · exact h m hm
    · rw [MvPolynomial.notMem_support_iff.1 hm]
      exact dvd_zero _
  obtain ⟨F', hF'⟩ := hd
  refine ⟨F.coeff i, F', hF', fun hmem => ?_⟩
  have h1 := MvPolynomial.mem_map_C_iff.1 hmem i
  have h2 : F.coeff i = F.coeff i * F'.coeff i := by
    conv_lhs => rw [hF', MvPolynomial.coeff_C_mul]
  have h3 : F'.coeff i = 1 :=
    (mul_left_cancel₀ (MvPolynomial.mem_support_iff.1 hi) ((mul_one _).trans h2)).symm
  rw [h3] at h1
  exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem mvPolynomial_content_valuationRing :
    ∀ (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] (g : ℕ), ((IsLocalRing.maximalIdeal O).map (MvPolynomial.C : O →+* MvPolynomial (Fin g) O)).IsPrime ∧ (∀ F : MvPolynomial (Fin g) O, F ≠ 0 → ∃ (π : O) (F' : MvPolynomial (Fin g) O), F = MvPolynomial.C π * F' ∧ F' ∉ (IsLocalRing.maximalIdeal O).map (MvPolynomial.C : O →+* MvPolynomial (Fin g) O)) ∧ ∀ (π : O) (u F : MvPolynomial (Fin g) O), u ∉ (IsLocalRing.maximalIdeal O).map (MvPolynomial.C : O →+* MvPolynomial (Fin g) O) → MvPolynomial.C π ∣ u * F → MvPolynomial.C π ∣ F := by
  intro O _ _ _ g
  have hp := mvPolynomial_map_maximalIdeal_isPrime O g
  refine ⟨hp, mvPolynomial_exists_content O g, fun π u F hu hdvd => ?_⟩
  by_cases hF : F = 0
  · rw [hF]; exact dvd_zero _
  obtain ⟨π', F', rfl, hF'⟩ := mvPolynomial_exists_content O g F hF
  have huF : u * F' ∉ (IsLocalRing.maximalIdeal O).map
      (MvPolynomial.C : O →+* MvPolynomial (Fin g) O) := fun h => (hp.mem_or_mem h).elim hu hF'
  rw [MvPolynomial.mem_map_C_iff, not_forall] at huF
  obtain ⟨m, hm⟩ := huF
  have hunit : IsUnit ((u * F').coeff m) := by
    by_contra hn
    exact hm ((IsLocalRing.mem_maximalIdeal _).2 hn)
  have h1 : π ∣ π' * (u * F').coeff m := by
    have := (MvPolynomial.C_dvd_iff_dvd_coeff _ _).1 hdvd m
    rwa [mul_left_comm, MvPolynomial.coeff_C_mul] at this
  have h2 : π ∣ π' := (hunit.dvd_mul_right).1 h1
  exact Dvd.dvd.mul_right (map_dvd _ h2) _

end GlobalTheory
