import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.SeamDefs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CrystallineSemistableComparison.Pb

open Polynomial

variable {K : Type} [Field K] {R : Type} [CommRing R] [IsDomain R] [Algebra K R]

theorem chart_ext_scale (A T : Subalgebra K R) (w : R) (hwA : w ∈ A)
    (hscale : ∀ x ∈ T, ∃ N : ℕ, w ^ N * x ∈ A) (g : R) (hg : IsIntegral T g) :
    ∃ N : ℕ, IsIntegral A (w ^ N * g) := by
  obtain ⟨p, hpm, hp⟩ := hg
  have hmono : ∀ (x : R) (n m : ℕ), n ≤ m → w ^ n * x ∈ A → w ^ m * x ∈ A := by
    intro x n m hnm hx
    have : w ^ m * x = w ^ (m - n) * (w ^ n * x) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hnm]
    rw [this]
    exact A.mul_mem (A.pow_mem hwA _) hx
  have hc : ∀ i : ℕ, ∃ n : ℕ, w ^ n * ((p.coeff i : T) : R) ∈ A := fun i =>
    hscale _ (p.coeff i).2
  choose n hn using hc
  set N : ℕ := ∑ i ∈ Finset.range (p.natDegree + 1), n i with hN
  have hcN : ∀ i ≤ p.natDegree, w ^ N * ((p.coeff i : T) : R) ∈ A := by
    intro i hi
    refine hmono _ (n i) N ?_ (hn i)
    exact Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
  set P : R[X] := p.map (algebraMap T R) with hP
  have hPm : P.Monic := hpm.map _
  have hPdeg : P.natDegree = p.natDegree := hpm.natDegree_map _
  have hPcoeff : ∀ i, P.coeff i = ((p.coeff i : T) : R) := fun i => by
    rw [hP, coeff_map]; rfl
  set Q : R[X] := P.scaleRoots (w ^ N) with hQ
  have hQm : Q.Monic := (monic_scaleRoots_iff _).2 hPm
  have hQlift : Q ∈ lifts (algebraMap A R) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    have hmem : Q.coeff i ∈ A := by
      rw [hQ, coeff_scaleRoots, hPdeg, hPcoeff]
      rcases lt_trichotomy i p.natDegree with hlt | heq | hgt
      · have h1 : (w ^ N) ^ (p.natDegree - i) = (w ^ N) ^ (p.natDegree - i - 1) * w ^ N := by
          rw [← pow_succ]; congr 1; omega
        rw [h1, mul_comm, mul_assoc]
        exact A.mul_mem (A.pow_mem (A.pow_mem hwA _) _) (hcN i hlt.le)
      · subst heq
        have : p.coeff p.natDegree = 1 := hpm.coeff_natDegree
        rw [this, Nat.sub_self, pow_zero, mul_one]
        exact A.one_mem
      · rw [coeff_eq_zero_of_natDegree_lt hgt]
        simp only [ZeroMemClass.coe_zero, zero_mul]
        exact A.zero_mem
    exact ⟨⟨_, hmem⟩, rfl⟩
  obtain ⟨q, hqQ, -, hqm⟩ := lifts_and_degree_eq_and_monic hQlift hQm
  refine ⟨N, q, hqm, ?_⟩
  rw [← eval_map, hqQ, hQ, scaleRoots_eval_mul, hP, eval_map, hp, mul_zero]

theorem chart_ext_pf (A T B0 Bu : Subalgebra K R) (hAT : A ≤ T) (hAB0 : A ≤ B0) (hB0 : B0 ≤ Bu) (hTBu : T ≤ Bu)
    (hB0FG : B0.FG) (hB0Int : ∀ b ∈ B0, IsIntegral A b) (hBuFG : Bu.FG) (hBuInt : ∀ b ∈ Bu, IsIntegral T b)
    (hFrac : ∀ r : R, ∃ b ∈ Bu, ∃ b' ∈ Bu, b' ≠ 0 ∧ r * b' = b)
    (w : R) (hwA : w ∈ A) (hw0 : w ≠ 0) (hscale : ∀ x ∈ T, ∃ N : ℕ, w ^ N * x ∈ A) :
    ∃ B' : Subalgebra K R, B0 ≤ B' ∧ B'.FG ∧ (∀ b ∈ B', IsIntegral A b) ∧
      ∀ r : R, ∃ b ∈ B', ∃ b' ∈ B', b' ≠ 0 ∧ r * b' = b := by
  classical
  obtain ⟨t, ht⟩ := hB0FG
  obtain ⟨s, hs⟩ := hBuFG
  have hkey : ∀ g : R, ∃ N : ℕ, g ∈ Bu → IsIntegral A (w ^ N * g) := by
    intro g
    by_cases hg : g ∈ Bu
    · obtain ⟨N, hN⟩ := chart_ext_scale A T w hwA hscale g (hBuInt g hg)
      exact ⟨N, fun _ => hN⟩
    · exact ⟨0, fun h => absurd h hg⟩
  choose N hN using hkey
  set u : Finset R := t ∪ s.image (fun g => w ^ N g * g) with hu
  set B' : Subalgebra K R := Algebra.adjoin K (u : Set R) with hB'
  have htB' : B0 ≤ B' := by
    rw [← ht, hB']
    exact Algebra.adjoin_mono (by rw [hu, Finset.coe_union]; exact Set.subset_union_left)
  have hwB' : w ∈ B' := htB' (hAB0 hwA)
  have hgen : ∀ g ∈ s, w ^ N g * g ∈ B' := by
    intro g hg
    apply Algebra.subset_adjoin
    rw [hu, Finset.coe_union]
    exact Or.inr (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hg))
  have hsBu : ∀ g ∈ s, g ∈ Bu := fun g hg => by
    rw [← hs]; exact Algebra.subset_adjoin (Finset.mem_coe.2 hg)

  have hpow : ∀ b ∈ Bu, ∃ L : ℕ, w ^ L * b ∈ B' := by
    intro b hb
    rw [← hs] at hb
    induction hb using Algebra.adjoin_induction with
    | mem x hx => exact ⟨N x, hgen x (Finset.mem_coe.1 hx)⟩
    | algebraMap k => exact ⟨0, by rw [pow_zero, one_mul]; exact B'.algebraMap_mem k⟩
    | add x y _ _ ihx ihy =>
      obtain ⟨L1, h1⟩ := ihx
      obtain ⟨L2, h2⟩ := ihy
      refine ⟨L1 + L2, ?_⟩
      have : w ^ (L1 + L2) * (x + y) = w ^ L2 * (w ^ L1 * x) + w ^ L1 * (w ^ L2 * y) := by ring
      rw [this]
      exact B'.add_mem (B'.mul_mem (B'.pow_mem hwB' _) h1) (B'.mul_mem (B'.pow_mem hwB' _) h2)
    | mul x y _ _ ihx ihy =>
      obtain ⟨L1, h1⟩ := ihx
      obtain ⟨L2, h2⟩ := ihy
      refine ⟨L1 + L2, ?_⟩
      have : w ^ (L1 + L2) * (x * y) = (w ^ L1 * x) * (w ^ L2 * y) := by ring
      rw [this]
      exact B'.mul_mem h1 h2
  refine ⟨B', htB', ⟨u, hB'.symm⟩, ?_, ?_⟩
  · intro b hb
    rw [hB'] at hb
    induction hb using Algebra.adjoin_induction with
    | mem x hx =>
      rw [hu, Finset.coe_union] at hx
      rcases hx with hx | hx
      · apply hB0Int
        rw [← ht]
        exact Algebra.subset_adjoin hx
      · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
        exact hN g (hsBu g hg)
    | algebraMap k =>
      have hk : algebraMap K R k ∈ A := A.algebraMap_mem k
      have : algebraMap K R k = algebraMap A R ⟨_, hk⟩ := rfl
      rw [this]
      exact isIntegral_algebraMap
    | add x y _ _ ihx ihy => exact ihx.add ihy
    | mul x y _ _ ihx ihy => exact ihx.mul ihy
  · intro r
    obtain ⟨b, hb, b', hb', hb'0, hrb⟩ := hFrac r
    obtain ⟨L1, h1⟩ := hpow b hb
    obtain ⟨L2, h2⟩ := hpow b' hb'
    refine ⟨w ^ (L1 + L2) * b, ?_, w ^ (L1 + L2) * b', ?_, ?_, ?_⟩
    · have : w ^ (L1 + L2) * b = w ^ L2 * (w ^ L1 * b) := by ring
      rw [this]; exact B'.mul_mem (B'.pow_mem hwB' _) h1
    · have : w ^ (L1 + L2) * b' = w ^ L1 * (w ^ L2 * b') := by ring
      rw [this]; exact B'.mul_mem (B'.pow_mem hwB' _) h2
    · exact mul_ne_zero (pow_ne_zero _ hw0) hb'0
    · rw [← hrb]; ring

end CrystallineSemistableComparison.Pb
