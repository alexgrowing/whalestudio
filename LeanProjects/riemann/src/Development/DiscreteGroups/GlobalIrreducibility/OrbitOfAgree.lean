import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.ExistsElliptic

open Polynomial GlobalTheory.GLq GlobalTheory.Published

noncomputable section

namespace DiscreteGroups.sglob.DzType.Kon

variable {g : ℕ} [Fact g.Prime] {n : ℕ} {K : Type} [Field K] [Algebra (ZMod g) K]

open scoped Classical in
theorem card_bad_le [Fintype K] [DecidableEq K] :
    (Finset.univ.filter fun z : Kˣ => ∃ i ∈ Finset.Icc 1 (n / 2), z ^ g ^ i = z).card ≤
      (n / 2) * g ^ (n / 2) := by
  have hg : 1 ≤ g := (Fact.out : g.Prime).one_lt.le
  calc (Finset.univ.filter fun z : Kˣ => ∃ i ∈ Finset.Icc 1 (n / 2), z ^ g ^ i = z).card
      ≤ ((Finset.Icc 1 (n / 2)).biUnion fun i => Finset.univ.filter fun z : Kˣ => z ^ g ^ i = z).card := by
        refine Finset.card_le_card fun z hz => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
        obtain ⟨i, hi, hzi⟩ := hz
        exact Finset.mem_biUnion.2 ⟨i, hi, by simp [hzi]⟩
    _ ≤ ∑ i ∈ Finset.Icc 1 (n / 2), (Finset.univ.filter fun z : Kˣ => z ^ g ^ i = z).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ i ∈ Finset.Icc 1 (n / 2), g ^ (n / 2) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' := Finset.mem_Icc.1 hi
        exact (card_fixed_le (K := K) i hi'.1).trans (Nat.pow_le_pow_right hg hi'.2)
    _ = (n / 2) * g ^ (n / 2) := by rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul, Nat.add_sub_cancel]

theorem orbit_of_agree (hn : 2 ≤ n) (hbig : 16 * n ^ 2 < g) (hK : Nat.card K = g ^ n) (θ θ' : Kˣ →* ℂˣ)
    (hθ : IsRegularChar g n θ)
    (h : ∀ z : Kˣ, (∃ y : Gn g n, Irreducible (y : Mt g n).charpoly ∧ aeval (z : K) (y : Mt g n).charpoly = 0) →
      fo g n θ z = fo g n θ' z) : ∃ i < n, θ' = θ ^ g ^ i := by
  classical
  have hgp : g.Prime := Fact.out
  have hg : 1 < g := hgp.one_lt
  have hn0 : 0 < n := by omega
  have hKpos : 0 < Nat.card K := by rw [hK]; exact pow_pos hgp.pos _
  have : Finite K := Nat.finite_of_card_ne_zero hKpos.ne'
  let _ : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = g ^ n := by rw [← Nat.card_eq_fintype_card, hK]
  have : FiniteDimensional (ZMod g) K := Module.Finite.of_finite
  have hfr : Module.finrank (ZMod g) K = n := by
    have h1 := Module.card_eq_pow_finrank (K := ZMod g) (V := K)
    rw [ZMod.card, hcard] at h1
    exact (Nat.pow_right_injective hgp.two_le h1).symm
  by_contra hno
  push_neg at hno
  have hne : ∀ i < n, ∀ j < n, θ ^ g ^ i ≠ θ' ^ g ^ j := by
    intro i hi j hj heq
    apply hno ((i + (n - j)) % n) (Nat.mod_lt _ hn0)
    have e1 : θ' = (θ' ^ g ^ j) ^ g ^ (n - j) := by
      rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hj.le, char_pow_period hcard θ' hgp.pos n, Nat.mod_self,
        pow_zero, pow_one]
    rw [e1, ← heq, ← pow_mul, ← pow_add, char_pow_period hcard θ hgp.pos]
  have hS' : ∑ z : Kˣ, fo g n θ z * fo g n θ' z⁻¹ = 0 := by
    rw [sum_fo_mul]
    refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_
    rw [if_neg (hne i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj))]
  have hS : ∑ z : Kˣ, fo g n θ z * fo g n θ z⁻¹ = (n : ℂ) * (Fintype.card Kˣ : ℂ) := by
    rw [sum_fo_mul]
    have e : ∀ i ∈ Finset.range n, (∑ j ∈ Finset.range n,
        if θ ^ g ^ i = θ ^ g ^ j then (Fintype.card Kˣ : ℂ) else 0) = Fintype.card Kˣ := by
      intro i hi
      rw [Finset.sum_eq_single i]
      · rw [if_pos rfl]
      · intro j hj hji
        rw [if_neg (fun h' => hji (hθ i j (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) h').symm)]
      · intro h'; exact absurd hi h'
    rw [Finset.sum_congr rfl e, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  set B := Finset.univ.filter fun z : Kˣ => ∃ i ∈ Finset.Icc 1 (n / 2), z ^ g ^ i = z with hB
  have hgood : ∀ z : Kˣ, z ∉ B → fo g n θ z⁻¹ = fo g n θ' z⁻¹ := by
    intro z hz
    apply h
    apply exists_elliptic hfr
    by_contra hd
    obtain ⟨i, hi, hzi⟩ := bad_of_deg hn0 hfr z⁻¹ hd
    apply hz
    simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨i, hi, ?_⟩
    rw [inv_pow] at hzi; exact inv_injective hzi
  have hdiff : (n : ℂ) * (Fintype.card Kˣ : ℂ) =
      ∑ z ∈ B, fo g n θ z * (fo g n θ z⁻¹ - fo g n θ' z⁻¹) := by
    rw [← hS, ← sub_zero (∑ z : Kˣ, fo g n θ z * fo g n θ z⁻¹), ← hS', ← Finset.sum_sub_distrib]
    rw [← Finset.sum_subset (Finset.subset_univ B)]
    · exact Finset.sum_congr rfl fun z _ => by ring
    · intro z _ hz; rw [hgood z hz]; ring
  have hnorm : (n : ℝ) * (Fintype.card Kˣ : ℝ) ≤ (B.card : ℝ) * ((n : ℝ) * (2 * n)) := by
    have h1 := congrArg norm hdiff
    rw [norm_mul, Complex.norm_natCast, Complex.norm_natCast] at h1
    rw [h1]
    refine (norm_sum_le _ _).trans ?_
    rw [← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun z _ => ?_
    rw [norm_mul]
    refine mul_le_mul (norm_fo_le g n θ z) ((norm_sub_le _ _).trans ?_) (norm_nonneg _) (Nat.cast_nonneg _)
    linarith [norm_fo_le g n θ z⁻¹, norm_fo_le g n θ' z⁻¹]
  have hU : Fintype.card Kˣ = g ^ n - 1 := by rw [Fintype.card_units, hcard]
  have hnat : n * (g ^ n - 1) ≤ B.card * (n * (2 * n)) := by
    rw [← hU]; exact_mod_cast hnorm
  have h2 : g ^ n - 1 ≤ B.card * (2 * n) := by
    have : n * (g ^ n - 1) ≤ n * (B.card * (2 * n)) := by
      calc n * (g ^ n - 1) ≤ B.card * (n * (2 * n)) := hnat
        _ = n * (B.card * (2 * n)) := by ring
    exact Nat.le_of_mul_le_mul_left this hn0
  have hcB := card_bad_le (g := g) (n := n) (K := K)
  set m := n / 2 with hm
  have hm2 : 2 * m ≤ n := Nat.mul_div_le n 2
  have hmn : m + 1 ≤ n := by omega
  have h3 : g ^ n - 1 ≤ n * n * g ^ m := by
    calc g ^ n - 1 ≤ B.card * (2 * n) := h2
      _ ≤ (m * g ^ m) * (2 * n) := Nat.mul_le_mul_right _ hcB
      _ = (2 * m) * n * g ^ m := by ring
      _ ≤ n * n * g ^ m := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hm2)
  have h4 : g ^ m * g ≤ g ^ n := by
    rw [← pow_succ]; exact Nat.pow_le_pow_right hgp.pos hmn
  have hgm : 0 < g ^ m := pow_pos hgp.pos _
  have h5 : g ^ m * (16 * n ^ 2 + 1) ≤ g ^ m * g := Nat.mul_le_mul_left _ hbig
  have h6 : n * n * g ^ m + 1 < g ^ n := by nlinarith
  omega

end DiscreteGroups.sglob.DzType.Kon
