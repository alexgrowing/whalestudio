import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift

noncomputable section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.Triang

variable {q : ℕ} [Fact q.Prime]

theorem bd_one_mul {f g : ℂ_[q]⟦X⟧} (hf : Bd 1 f) (hg : Bd 1 g) : Bd 1 (f * g) := by
  intro n
  rw [PowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun p _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hf _) (norm_nonneg _) (hg _)

theorem bd_one_pow {f : ℂ_[q]⟦X⟧} (hf : Bd 1 f) (n : ℕ) : Bd 1 (f ^ n) := by
  induction n with
  | zero =>
    intro m
    rw [pow_zero, PowerSeries.coeff_one]
    split_ifs <;> simp
  | succ n ih =>
    rw [pow_succ]
    exact bd_one_mul ih hf

theorem norm_le_of_distinct {ι : Type*} (s : Finset ι) (e : ι → ℕ) (u : ι → ℂ_[q]⟦X⟧) (c : ι → ℂ_[q]) (B : ℝ)
    (he : Set.InjOn e s) (hu : ∀ j ∈ s, Bd 1 (u j)) (h0 : ∀ j ∈ s, ‖constantCoeff (u j)‖ = 1)
    (hB : Bd B (∑ j ∈ s, C (c j) * (X ^ e j * u j))) : ∀ j ∈ s, ‖c j‖ ≤ B := by
  classical
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hcoeff : ∀ N, coeff N (∑ j ∈ s, C (c j) * (X ^ e j * u j)) =
      ∑ j ∈ s, c j * (if e j ≤ N then coeff (N - e j) (u j) else 0) := by
    intro N
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  have key : ∀ N, ∀ j ∈ s, e j = N → ‖c j‖ ≤ B := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
    intro j hj hjN
    have hsplit := (hcoeff N).trans (Finset.add_sum_erase s _ hj).symm
    beta_reduce at hsplit
    have hjterm : c j * (if e j ≤ N then coeff (N - e j) (u j) else 0) = c j * constantCoeff (u j) := by
      rw [if_pos hjN.le, hjN, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    have hrest : ‖∑ i ∈ s.erase j, c i * (if e i ≤ N then coeff (N - e i) (u i) else 0)‖ ≤ B := by
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB0 fun i hi => ?_
      obtain ⟨hij, his⟩ := Finset.mem_erase.mp hi
      split_ifs with hle
      · have hlt : e i < N := lt_of_le_of_ne hle fun h => hij (he his hj (h.trans hjN.symm))
        rw [norm_mul]
        calc ‖c i‖ * ‖coeff (N - e i) (u i)‖ ≤ B * 1 :=
              mul_le_mul (ih _ hlt i his rfl) (hu i his _) (norm_nonneg _) hB0
          _ = B := mul_one B
      · simpa using hB0
    have hmain : c j * constantCoeff (u j) = coeff N (∑ j ∈ s, C (c j) * (X ^ e j * u j)) -
        ∑ i ∈ s.erase j, c i * (if e i ≤ N then coeff (N - e i) (u i) else 0) := by
      linear_combination -hsplit - hjterm
    have hnorm : ‖c j‖ = ‖c j * constantCoeff (u j)‖ := by rw [norm_mul, h0 j hj, mul_one]
    rw [hnorm, hmain, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hB N) ?_)
    rwa [norm_neg]
  exact fun j hj => key (e j) j hj rfl

theorem coeff_norm_le : ∀ (q : ℕ) [Fact q.Prime] (xs ys : ℂ_[q]⟦X⟧) (k : ℕ) (a b : ℕ → ℂ_[q]) (B : ℝ), Bd 1 xs → Bd 1 ys → ‖constantCoeff xs‖ = 1 → ‖constantCoeff ys‖ = 1 → Bd B (∑ i ∈ Finset.range (k + 1), (C (a i) * X ^ (2 * (k - i) + 3) * xs ^ i + C (b i) * X ^ (2 * (k - i)) * xs ^ i * ys)) → ∀ i ≤ k, ‖a i‖ ≤ B ∧ ‖b i‖ ≤ B := by
  intro q _ xs ys k a b B hxs hys hx0 hy0 hB
  classical
  let s : Finset (Bool × ℕ) := Finset.univ ×ˢ Finset.range (k + 1)
  let e : Bool × ℕ → ℕ := fun j => bif j.1 then 2 * (k - j.2) + 3 else 2 * (k - j.2)
  let u : Bool × ℕ → ℂ_[q]⟦X⟧ := fun j => bif j.1 then xs ^ j.2 else xs ^ j.2 * ys
  let c : Bool × ℕ → ℂ_[q] := fun j => bif j.1 then a j.2 else b j.2
  have hmem : ∀ {j : Bool × ℕ}, j ∈ s → j.2 < k + 1 := fun hj =>
    Finset.mem_range.mp (Finset.mem_product.mp hj).2
  have he : Set.InjOn e s := by
    rintro ⟨b₁, i₁⟩ h₁ ⟨b₂, i₂⟩ h₂ heq
    have hi₁ := hmem (Finset.mem_coe.mp h₁)
    have hi₂ := hmem (Finset.mem_coe.mp h₂)
    cases b₁ <;> cases b₂ <;> simp only [e, cond_true, cond_false] at heq hi₁ hi₂ <;>
      first | (exfalso; omega) | (congr 1; omega)
  have hu : ∀ j ∈ s, Bd 1 (u j) := by
    rintro ⟨_ | _, i⟩ _
    · exact bd_one_mul (bd_one_pow hxs i) hys
    · exact bd_one_pow hxs i
  have h0 : ∀ j ∈ s, ‖constantCoeff (u j)‖ = 1 := by
    rintro ⟨_ | _, i⟩ _
    · show ‖constantCoeff (xs ^ i * ys)‖ = 1
      rw [map_mul, map_pow, norm_mul, norm_pow, hx0, hy0, one_pow, one_mul]
    · show ‖constantCoeff (xs ^ i)‖ = 1
      rw [map_pow, norm_pow, hx0, one_pow]
  have hsum : (∑ j ∈ s, C (c j) * (X ^ e j * u j)) = ∑ i ∈ Finset.range (k + 1),
      (C (a i) * X ^ (2 * (k - i) + 3) * xs ^ i + C (b i) * X ^ (2 * (k - i)) * xs ^ i * ys) := by
    simp only [s]
    rw [Finset.sum_product, Fintype.sum_bool, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [e, u, c, cond_true, cond_false]
    ring
  have hB' : Bd B (∑ j ∈ s, C (c j) * (X ^ e j * u j)) := by
    rw [hsum]
    exact hB
  have key := norm_le_of_distinct s e u c B he hu h0 hB'
  intro i hi
  have hi' : i ∈ Finset.range (k + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hi)
  exact ⟨key (true, i) (Finset.mem_product.mpr ⟨Finset.mem_univ _, hi'⟩),
    key (false, i) (Finset.mem_product.mpr ⟨Finset.mem_univ _, hi'⟩)⟩

end GlobalTheory.MomOne.Triang
