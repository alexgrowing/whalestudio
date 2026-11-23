import Mathlib
import GroundTheory.PAdicHodge.BCrisNewtonApprox
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace WittTilt

open _root_.WittVector Laurent ACris

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p] [CharZero K]

local notation "𝔸" => Localization.Away (p : AInf K p)

variable {ρ : ℝ}

theorem gn_sum_lt (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {ι : Type*} (s : Finset ι) (f : ι → 𝔸) {M : ℝ}
    (hM : 0 < M) (h : ∀ i ∈ s, gn K p ρ (f i) < M) : gn K p ρ (∑ i ∈ s, f i) < M := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, gn_zero]; exact hM
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (gn_add_le hρ0 hρ1 _ _).trans_lt (max_lt (h i (Finset.mem_insert_self i s))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk)))

theorem sum_sub_sum_mem {R : Type*} [CommRing R] (I : Ideal R) (d : ℕ) (C : ℕ → R) {a a' b b' : R}
    (ha : a - a' ∈ I) (hb : b - b' ∈ I) :
    ∑ i ∈ Finset.range (d + 1), C i * a ^ i * b ^ (d - i) -
      ∑ i ∈ Finset.range (d + 1), C i * a' ^ i * b' ^ (d - i) ∈ I := by
  rw [← Ideal.Quotient.eq]
  simp only [map_sum, map_mul, map_pow, Ideal.Quotient.eq.2 ha, Ideal.Quotient.eq.2 hb]

theorem algebraMap_acrisZero_algebraMap (w : AInf K p) :
    algebraMap (ACrisZero K p) (ACris K p) (algebraMap (AInf K p) (ACrisZero K p) w) =
      algebraMap (AInf K p) (ACris K p) w :=
  rfl

set_option maxHeartbeats 4000000 in

theorem false_of_dominant (hp0 : ‖(p : K)‖ ≤ ρ) (hρ1 : ρ < 1) {a b : ACris K p} {Na Nb : ℕ}
    {Fa Fb : ℝ}
    (hsa : ∀ N ≥ Na, ∀ c : ACrisZero K p,
      a - algebraMap _ (ACris K p) c ∈ Ideal.span {(p : ACris K p) ^ N} → gn K p ρ (c : 𝔸) = Fa)
    (hsb : ∀ N ≥ Nb, ∀ c : ACrisZero K p,
      b - algebraMap _ (ACris K p) c ∈ Ideal.span {(p : ACris K p) ^ N} → gn K p ρ (c : 𝔸) = Fb)
    (d : ℕ) (x : ℕ → AInf K p)
    (hsum : ∑ i ∈ Finset.range (d + 1),
      algebraMap (AInf K p) (ACris K p) (x i) * a ^ i * b ^ (d - i) = 0)
    {j : ℕ} (hj : j ∈ Finset.range (d + 1))
    (hpos : 0 < gn K p ρ (algebraMap (AInf K p) 𝔸 (x j)) * Fa ^ j * Fb ^ (d - j))
    (hdom : ∀ i ∈ Finset.range (d + 1), i ≠ j →
      gn K p ρ (algebraMap (AInf K p) 𝔸 (x i)) * Fa ^ i * Fb ^ (d - i) <
        gn K p ρ (algebraMap (AInf K p) 𝔸 (x j)) * Fa ^ j * Fb ^ (d - j)) : False := by
  have hρ0 : 0 < ρ := norm_p_pos.trans_le hp0
  set g := fun i => gn K p ρ (algebraMap (AInf K p) 𝔸 (x i)) * Fa ^ i * Fb ^ (d - i) with hg
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos hρ1
  set N := max n (max Na Nb)
  have hN : ρ ^ N < g j := (pow_le_pow_of_le_one hρ0.le hρ1.le (le_max_left _ _)).trans_lt hn
  obtain ⟨ca, hca⟩ := exists_approx a N
  obtain ⟨cb, hcb⟩ := exists_approx b N
  have hFa := hsa N ((le_max_left _ _).trans (le_max_right _ _)) ca hca
  have hFb := hsb N ((le_max_right _ _).trans (le_max_right _ _)) cb hcb
  set T : ℕ → ACrisZero K p := fun i => algebraMap (AInf K p) (ACrisZero K p) (x i) * ca ^ i * cb ^ (d - i)
  set S : ACrisZero K p := ∑ i ∈ Finset.range (d + 1), T i

  have hS : algebraMap _ (ACris K p) (0 : ACrisZero K p) - algebraMap _ (ACris K p) S ∈
      Ideal.span {(p : ACris K p) ^ N} := by
    have eS : algebraMap (ACrisZero K p) (ACris K p) S = ∑ i ∈ Finset.range (d + 1),
        algebraMap (AInf K p) (ACris K p) (x i) * algebraMap (ACrisZero K p) (ACris K p) ca ^ i *
          algebraMap (ACrisZero K p) (ACris K p) cb ^ (d - i) := by
      simp only [S, T, map_sum, map_mul, map_pow, algebraMap_acrisZero_algebraMap]
    have key := sum_sub_sum_mem (Ideal.span {(p : ACris K p) ^ N}) d
      (fun i => algebraMap (AInf K p) (ACris K p) (x i)) hca hcb
    rw [hsum, zero_sub, ← eS] at key
    rw [map_zero, zero_sub]
    exact key
  have hle := gn_sub_le_of_mem hp0 hρ1 hS
  rw [ZeroMemClass.coe_zero, zero_sub, gn_neg hρ0 hρ1] at hle

  have hT : ∀ i, gn K p ρ ((T i : ACrisZero K p) : 𝔸) = g i := by
    intro i
    simp only [T, MulMemClass.coe_mul, SubmonoidClass.coe_pow]
    rw [gn_mul hρ0 hρ1, gn_mul hρ0 hρ1, gn_pow hρ0 hρ1, gn_pow hρ0 hρ1, hFa, hFb]
    rfl
  have hSsum : ((S : ACrisZero K p) : 𝔸) = ∑ i ∈ Finset.range (d + 1), ((T i : ACrisZero K p) : 𝔸) := by
    simp only [S]
    push_cast
    rfl
  have hrest : gn K p ρ (∑ i ∈ (Finset.range (d + 1)).erase j, ((T i : ACrisZero K p) : 𝔸)) < g j :=
    gn_sum_lt hρ0 hρ1 _ _ hpos fun i hi => by
      rw [hT]
      exact hdom i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)
  have hsplit : ((S : ACrisZero K p) : 𝔸) = ((T j : ACrisZero K p) : 𝔸) +
      ∑ i ∈ (Finset.range (d + 1)).erase j, ((T i : ACrisZero K p) : 𝔸) := by
    rw [hSsum, Finset.add_sum_erase _ (fun i => ((T i : ACrisZero K p) : 𝔸)) hj]
  have hSj : gn K p ρ ((S : ACrisZero K p) : 𝔸) = g j := by
    rw [← hT j]
    refine gn_eq_of_gn_sub_lt hρ0 hρ1 ?_
    rw [hsplit, sub_add_cancel_left, gn_neg hρ0 hρ1, hT j]
    exact hrest
  linarith

end WittTilt

end GroundTheory.PAdicHodge
