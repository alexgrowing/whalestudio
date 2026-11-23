import Mathlib

open Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.T2

theorem pow_key (x : ℝ) (hx0 : 0 < x) (a k : ℕ) (hka : k ≤ a) :
    x ^ (a + k) ≤ (5 * x) ^ a * (x / 5) ^ k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hka
  have hx : (5 * x) ^ (k + m) * (x / 5) ^ k = 5 ^ m * x ^ (k + m + k) := by
    rw [mul_pow, div_pow]
    field_simp
    ring
  rw [hx]
  have h1 : (1 : ℝ) ≤ 5 ^ m := one_le_pow₀ (by norm_num)
  exact le_mul_of_one_le_left (by positivity) h1

theorem prodDist_step {ι : Type*} [DecidableEq ι] (t : ι → ℝ) (s S : Finset ι) (hS : S ⊆ s)
    (h3 : 3 * S.card ≤ s.card) (r ρ : ℝ) (hr : 0 < r)
    (hfar : ∀ j ∈ s, j ∉ S → r / 5 ≤ |ρ - t j|)
    (hin : ((r / 5) / 25) ^ S.card ≤ ∏ j ∈ S, |ρ - t j|) :
    (r / 25) ^ s.card ≤ ∏ j ∈ s, |ρ - t j| := by
  have hsplit : (∏ j ∈ s \ S, |ρ - t j|) * ∏ j ∈ S, |ρ - t j| = ∏ j ∈ s, |ρ - t j| :=
    Finset.prod_sdiff hS
  have hfar' : (r / 5) ^ (s \ S).card ≤ ∏ j ∈ s \ S, |ρ - t j| := by
    calc (r / 5) ^ (s \ S).card = ∏ _j ∈ s \ S, (r / 5) := (Finset.prod_const _).symm
      _ ≤ ∏ j ∈ s \ S, |ρ - t j| := by
        apply Finset.prod_le_prod
        · intro i _
          positivity
        · intro i hi
          rw [Finset.mem_sdiff] at hi
          exact hfar i hi.1 hi.2
  have hcard : (s \ S).card + S.card = s.card := Finset.card_sdiff_add_card_eq_card hS
  have hka : S.card ≤ (s \ S).card := by omega
  have key := pow_key (r / 25) (by positivity) (s \ S).card S.card hka
  calc (r / 25) ^ s.card = (r / 25) ^ ((s \ S).card + S.card) := by rw [hcard]
    _ ≤ (5 * (r / 25)) ^ (s \ S).card * (r / 25 / 5) ^ S.card := key
    _ = (r / 5) ^ (s \ S).card * ((r / 5) / 25) ^ S.card := by
        rw [show 5 * (r / 25) = r / 5 by ring, show r / 25 / 5 = r / 5 / 25 by ring]
    _ ≤ (∏ j ∈ s \ S, |ρ - t j|) * ∏ j ∈ S, |ρ - t j| :=
        mul_le_mul hfar' hin (by positivity)
          (Finset.prod_nonneg (fun i _ => abs_nonneg _))
    _ = ∏ j ∈ s, |ρ - t j| := hsplit

private theorem exists_center_near_with_few_points_close {ι : Type*} (t : ι → ℝ) (s : Finset ι) (c r : ℝ)
    (hr : 0 < r) :
    ∃ c' : ℝ, |c' - c| ≤ 4 * r / 5 ∧
      3 * (s.filter (fun j => |t j - c'| < 2 * r / 5)).card ≤ s.card := by
  classical
  set S1 := s.filter (fun j => |t j - (c - 4 * r / 5)| < 2 * r / 5) with hS1
  set S2 := s.filter (fun j => |t j - c| < 2 * r / 5) with hS2
  set S3 := s.filter (fun j => |t j - (c + 4 * r / 5)| < 2 * r / 5) with hS3
  have d12 : Disjoint S1 S2 := by
    rw [hS1, hS2, Finset.disjoint_filter]
    intro j _ h1 h2
    rw [abs_lt] at h1 h2
    linarith [h1.1, h1.2, h2.1, h2.2]
  have d13 : Disjoint S1 S3 := by
    rw [hS1, hS3, Finset.disjoint_filter]
    intro j _ h1 h2
    rw [abs_lt] at h1 h2
    linarith [h1.1, h1.2, h2.1, h2.2]
  have d23 : Disjoint S2 S3 := by
    rw [hS2, hS3, Finset.disjoint_filter]
    intro j _ h1 h2
    rw [abs_lt] at h1 h2
    linarith [h1.1, h1.2, h2.1, h2.2]
  have hsub : S1 ∪ S2 ∪ S3 ⊆ s :=
    Finset.union_subset (Finset.union_subset (Finset.filter_subset _ _)
      (Finset.filter_subset _ _)) (Finset.filter_subset _ _)
  have hsum : S1.card + S2.card + S3.card ≤ s.card := by
    have h := Finset.card_le_card hsub
    rwa [Finset.card_union_of_disjoint (Finset.disjoint_union_left.2 ⟨d13, d23⟩),
      Finset.card_union_of_disjoint d12] at h
  by_cases h1 : 3 * S1.card ≤ s.card
  · refine ⟨c - 4 * r / 5, ?_, h1⟩
    rw [abs_le]
    constructor <;> linarith
  by_cases h2 : 3 * S2.card ≤ s.card
  · refine ⟨c, ?_, h2⟩
    rw [abs_le]
    constructor <;> linarith
  · refine ⟨c + 4 * r / 5, ?_, ?_⟩
    · rw [abs_le]
      constructor <;> linarith
    · have h3' : 3 * S3.card ≤ s.card := by omega
      exact h3'

theorem exists_far_from_points {ι : Type*} [DecidableEq ι] (t : ι → ℝ) :
    ∀ (N : ℕ) (s : Finset ι), s.card = N → ∀ (c r : ℝ), 0 < r →
      ∃ ρ : ℝ, |ρ - c| ≤ r ∧ (r / 25) ^ s.card ≤ ∏ j ∈ s, |ρ - t j| := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro s hs c r hr
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · subst h0
      rw [Finset.card_eq_zero] at hs
      subst hs
      refine ⟨c, by simp [hr.le], by simp⟩
    · obtain ⟨c', hc', h3⟩ := exists_center_near_with_few_points_close t s c r hr
      set S := s.filter (fun j => |t j - c'| < 2 * r / 5) with hSdef
      have hlt : S.card < N := by omega
      obtain ⟨ρ, hρ, hin⟩ := ih S.card hlt S rfl c' (r / 5) (by positivity)
      refine ⟨ρ, ?_, prodDist_step t s S (Finset.filter_subset _ _) h3 r ρ hr ?_ hin⟩
      · calc |ρ - c| ≤ |ρ - c'| + |c' - c| := abs_sub_le ρ c' c
          _ ≤ r / 5 + 4 * r / 5 := add_le_add hρ hc'
          _ = r := by ring
      · intro j hj hjS
        have hn : 2 * r / 5 ≤ |t j - c'| :=
          not_lt.mp (fun h => hjS (Finset.mem_filter.2 ⟨hj, h⟩))
        have htri : |t j - c'| ≤ |t j - ρ| + |ρ - c'| := abs_sub_le (t j) ρ c'
        rw [abs_sub_comm (t j) ρ] at htri
        linarith

theorem prodDist {ι : Type*} [DecidableEq ι] (t : ι → ℝ) (s : Finset ι) (c r : ℝ) (hr : 0 < r) :
    ∃ ρ : ℝ, |ρ - c| ≤ r ∧ (r / 25) ^ s.card ≤ ∏ j ∈ s, |ρ - t j| :=
  exists_far_from_points t s.card s rfl c r hr

end Formalism.HermitianLattices.Ext.PrimesInProgressions.T2
