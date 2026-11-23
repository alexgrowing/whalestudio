import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedValA
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedValB
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedKerProd
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedKurOmega
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.G2EqZeroOfHasCMByThree

noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F

namespace ReciprocityTheory.ChartRestriction.L1

theorem three_dvd_of_norm_relations (l x : ℝ) (hl : 1 < l) (hx : 0 < x) (n a : ℤ) (t : ℕ)
    (h1 : x ^ 12 * (l ^ n) ^ 2 = 1) (h2 : x ^ (2 * t) * l ^ a = 1) (ht : ¬ 3 ∣ t) :
    ∃ m : ℤ, n = 3 * m := by
  have hl0 : 0 < l := by linarith
  have e1 : x ^ (12 * t) * l ^ (2 * n * t) = 1 := by
    have : (x ^ 12 * (l ^ n) ^ 2) ^ t = 1 := by rw [h1, one_pow]
    rw [mul_pow, ← pow_mul] at this
    rw [← this]
    congr 1
    rw [← zpow_natCast (l ^ n) 2, ← zpow_mul, ← zpow_natCast _ t, ← zpow_mul]
    congr 1
    push_cast
    ring
  have e2 : x ^ (12 * t) * l ^ (6 * a) = 1 := by
    have : (x ^ (2 * t) * l ^ a) ^ 6 = 1 := by rw [h2, one_pow]
    rw [mul_pow, ← pow_mul] at this
    rw [← this]
    congr 1
    · congr 1
      ring
    · rw [← zpow_natCast (l ^ a) 6, ← zpow_mul]
      congr 1
      push_cast
      ring
  have hx0 : x ^ (12 * t) ≠ 0 := (pow_pos hx _).ne'
  have e3 : l ^ (2 * n * t) = l ^ (6 * a) := mul_left_cancel₀ hx0 (e1.trans e2.symm)
  have e4 : 2 * n * t = 6 * a := zpow_right_injective₀ hl0 hl.ne' e3
  have e5 : (3 : ℤ) ∣ n * t := ⟨a, by linarith⟩
  have hp : Prime (3 : ℤ) := Int.prime_three
  rcases hp.dvd_or_dvd e5 with h | h
  · exact h
  · exact absurd (by exact_mod_cast h) ht

section Norms

variable (l : ℕ) [Fact l.Prime]

theorem norm_twentySeven_eq_one_of_five_le (h5 : 5 ≤ l) : ‖(27 : ℂ_[l])‖ = 1 := by
  have h : ¬ l ∣ 27 := by
    intro h
    have h3 : l ∣ 3 := (Fact.out : l.Prime).dvd_of_dvd_pow (show l ∣ 3 ^ 3 by simpa using h)
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  simpa using red_norm_natCast l h

theorem norm_1728_eq_one_of_five_le' (h5 : 5 ≤ l) : ‖(1728 : ℂ_[l])‖ = 1 := by
  have h : ¬ l ∣ 1728 := by
    intro h
    have h' : l ∣ 2 ^ 6 * 3 ^ 3 := by simpa using h
    rcases (Fact.out : l.Prime).dvd_mul.1 h' with h2 | h3
    · have := Nat.le_of_dvd (by norm_num) ((Fact.out : l.Prime).dvd_of_dvd_pow h2)
      omega
    · have := Nat.le_of_dvd (by norm_num) ((Fact.out : l.Prime).dvd_of_dvd_pow h3)
      omega
  simpa using red_norm_natCast l h

theorem norm_sub_1728_eq_one_of_norm_lt_one (h5 : 5 ≤ l) {J : ℂ_[l]} (hJ : ‖J‖ < 1) : ‖J - 1728‖ = 1 := by
  have h := norm_1728_eq_one_of_five_le' l h5
  have hne : ‖J‖ ≠ ‖-(1728 : ℂ_[l])‖ := by rw [norm_neg, h]; exact hJ.ne
  rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_neg, h]
  exact max_eq_right hJ.le

theorem norm_weierstrass_coeff_small_j (h5 : 5 ≤ l) {J : ℂ_[l]} (hJ : ‖J‖ < 1) :
    ‖27 * J / (J - 1728)‖ = ‖J‖ ∧
      ‖(27 * J / (J - 1728)) ^ 3 - 27 * (27 * J / (J - 1728)) ^ 2‖ = ‖J‖ ^ 2 := by
  have h1 := norm_sub_1728_eq_one_of_norm_lt_one l h5 hJ
  have h27 := norm_twentySeven_eq_one_of_five_le l h5
  have h1728 := norm_1728_eq_one_of_five_le' l h5
  have hne : J - 1728 ≠ 0 := by
    intro h
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  have hc : ‖27 * J / (J - 1728)‖ = ‖J‖ := by
    rw [norm_div, norm_mul, h1, h27, one_mul, div_one]
  refine ⟨hc, ?_⟩
  have e : (27 * J / (J - 1728)) ^ 3 - 27 * (27 * J / (J - 1728)) ^ 2
      = (27 * J / (J - 1728)) ^ 2 * (27 * 1728 / (J - 1728)) := by
    field_simp
    ring
  rw [e, norm_mul, norm_pow, hc, norm_div, norm_mul, h1, h27, h1728]
  norm_num

end Norms

theorem valDiv3 (d : ℕ) (L : PeriodPair) (hsq : Squarefree d) (hd4 : d % 4 = 3) (hCM : HasCMBy d L) (l : ℕ)
    [Fact l.Prime] (h5 : 5 ≤ l) (hld : ¬ l ∣ d) (ι : ℂ ≃+* ℂ_[l]) (hJ : ι (jInv L) ∈ MaximalUnramifiedExtension l)
    (hJ1 : ‖ι (jInv L)‖ ≤ 1) (h0 : ι (jInv L) ≠ 0) :
    ∃ m : ℤ, ‖ι (jInv L)‖ = (l : ℝ) ^ (3 * m) := by
  rcases hJ1.eq_or_lt with hJ1 | hJ1
  · exact ⟨0, by simpa using hJ1⟩
  have hj0 : jInv L ≠ 0 := fun h => h0 (by rw [h, map_zero])
  have hg2 : L.g₂ ≠ 0 := fun h => hj0 ((jInv_eq_zero_iff L).2 h)
  have hd3 : d ≠ 3 := by
    rintro rfl
    exact hg2 (g2_eq_zero_of_hasCMBy_three L hCM)
  have hsub := norm_sub_1728_eq_one_of_norm_lt_one l h5 hJ1
  have i27 : ι 27 = 27 := map_ofNat ι 27
  have i1728 : ι 1728 = 1728 := map_ofNat ι 1728
  have hg3 : L.g₃ ≠ 0 := by
    intro h
    have h' := (jInv_eq_iff L).2 h
    rw [h', i1728, sub_self, norm_zero] at hsub
    exact zero_ne_one hsub
  obtain ⟨L0, hCM0, hj, hc2, hc3⟩ := exists_cm_lattice_equal_invariants d L hCM hg2 hg3
  set J : ℂ_[l] := ι (jInv L) with hJdef
  have hι2 : ι L0.g₂ = 27 * J / (J - 1728) := by
    rw [hc2]; simp [hJdef, i27, i1728]
  have hι3 : ι L0.g₃ = 27 * J / (J - 1728) := by
    rw [hc3]; simp [hJdef, i27, i1728]
  obtain ⟨hnc, hnD⟩ := norm_weierstrass_coeff_small_j l h5 hJ1
  set c : ℂ_[l] := 27 * J / (J - 1728) with hcdef
  have hιD : ι (L0.g₂ ^ 3 - 27 * L0.g₃ ^ 2) = c ^ 3 - 27 * c ^ 2 := by
    simp [hι2, hι3, i27]
  have hJpos : 0 < ‖J‖ := norm_pos_iff.2 h0
  have hD0 : c ^ 3 - 27 * c ^ 2 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnD
    exact (pow_pos hJpos 2).ne hnD
  obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq (c ^ 3 - 27 * c ^ 2)⁻¹ (n := 12) (by norm_num)
  have hμ1 : μ ^ 12 * ι (L0.g₂ ^ 3 - 27 * L0.g₃ ^ 2) = 1 := by
    rw [hιD, hμ, inv_mul_cancel₀ hD0]
  have hμn : ‖μ‖ ^ 12 * ‖J‖ ^ 2 = 1 := by
    have := congrArg norm hμ1
    rwa [hιD, norm_mul, norm_pow, hnD, norm_one] at this
  have hμpos : 0 < ‖μ‖ := by
    rcases (norm_nonneg μ).eq_or_lt with h | h
    · rw [← h] at hμn
      norm_num at hμn
    · exact h
  have hn4 : ‖μ ^ 4 * ι L0.g₂‖ < 1 := by
    have e : ‖μ ^ 4 * ι L0.g₂‖ ^ 3 = ‖J‖ := by
      rw [hι2, norm_mul, norm_pow, hnc]
      calc (‖μ‖ ^ 4 * ‖J‖) ^ 3 = (‖μ‖ ^ 12 * ‖J‖ ^ 2) * ‖J‖ := by ring
        _ = ‖J‖ := by rw [hμn, one_mul]
    by_contra hcon
    have : 1 ≤ ‖μ ^ 4 * ι L0.g₂‖ ^ 3 := one_le_pow₀ (not_lt.1 hcon)
    rw [e] at this
    exact absurd hJ1 (not_lt.2 this)
  have hn6 : ‖μ ^ 6 * ι L0.g₃‖ = 1 := by
    have e : ‖μ ^ 6 * ι L0.g₃‖ ^ 2 = 1 := by
      rw [hι3, norm_mul, norm_pow, hnc]
      calc (‖μ‖ ^ 6 * ‖J‖) ^ 2 = ‖μ‖ ^ 12 * ‖J‖ ^ 2 := by ring
        _ = 1 := hμn
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 e
  obtain ⟨N, T, hlN, h3N, h3T, hT, hk⟩ :=
    kerProd d L0 hsq hd4 hCM0 l Fact.out h5 hld 3 (Or.inr ⟨rfl, hd3⟩)
  have hunit := unit_prod L0 l ι h5 μ hμ1 hn4.le hn6.le 3 N (Or.inl ⟨rfl, hn4⟩) hlN h3N T hT
  have hcK : c ∈ MaximalUnramifiedExtension l := by
    have h27 : (27 : ℂ_[l]) ∈ MaximalUnramifiedExtension l := by
      exact_mod_cast natCast_mem (MaximalUnramifiedExtension l) 27
    have h1728 : (1728 : ℂ_[l]) ∈ MaximalUnramifiedExtension l := by
      exact_mod_cast natCast_mem (MaximalUnramifiedExtension l) 1728
    exact div_mem (mul_mem h27 hJ) (sub_mem hJ h1728)
  have hP : ι (∏ z ∈ T, L0.weierstrassP z) ∈ MaximalUnramifiedExtension l := by
    have := hk ((MaximalUnramifiedExtension l).comap (ι : ℂ →+* ℂ_[l]))
      (by rw [Subfield.mem_comap]; simpa [hι2] using hcK)
      (by rw [Subfield.mem_comap]; simpa [hι3] using hcK)
      (by rw [Subfield.mem_comap]; exact omega_mem_kur d hsq hd4 l hld ι)
    simpa [Subfield.mem_comap] using this
  have hP0 : ι (∏ z ∈ T, L0.weierstrassP z) ≠ 0 := by
    intro h
    rw [h, norm_zero, mul_zero] at hunit
    exact zero_ne_one hunit
  obtain ⟨a, ha⟩ := kur_val l hP hP0
  obtain ⟨n, hn⟩ := kur_val l hJ h0
  have hl1 : (1 : ℝ) < l := by
    have : 1 < l := by omega
    exact_mod_cast this
  rw [ha] at hunit
  rw [hn] at hμn
  obtain ⟨m, hm⟩ := three_dvd_of_norm_relations l ‖μ‖ hl1 hμpos n a T.card hμn hunit h3T
  exact ⟨m, by rw [hn, hm]⟩

end ReciprocityTheory.ChartRestriction.L1
