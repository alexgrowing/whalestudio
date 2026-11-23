import Mathlib
import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects

open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GlobalTheory.CompanionTheory.Ar.Num (dotDual)

namespace PositivityTheory.Xgn.HodgeDualOverlap

theorem mem_dotDual {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] (R : Subalgebra O Ω) {r : ℕ}
    (L : AddSubgroup (Fin r → Ω)) (e : Fin r → Ω) :
    e ∈ dotDual R L ↔ ∀ l ∈ L, l ⬝ᵥ e ∈ R := by
  simp [dotDual, AddSubgroup.mem_iInf]

end PositivityTheory.Xgn.HodgeDualOverlap

private theorem exists_div_pow_mul_mem_chartRing {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] {ι : Type}
    (x : ι → Ω) (i j : ι) (hi : x i ≠ 0) (y : Ω) (hy : y ∈ chartRing O x i) :
    ∃ d : ℕ, (x i / x j) ^ d * y ∈ chartRing O x j := by
  have hq : x i / x j ∈ chartRing O x j := Algebra.subset_adjoin ⟨i, rfl⟩
  have mono : ∀ z : Ω, ∀ d n : ℕ, d ≤ n → (x i / x j) ^ d * z ∈ chartRing O x j →
      (x i / x j) ^ n * z ∈ chartRing O x j := by
    intro z d n hdn hz
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hdn
    rw [pow_add, mul_comm ((x i / x j) ^ d), mul_assoc]
    exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hq _) hz
  induction hy using Algebra.adjoin_induction with
  | mem z hz =>
    obtain ⟨t, rfl⟩ := hz
    refine ⟨1, ?_⟩
    have h : (x i / x j) ^ 1 * (x t / x i) = x t / x j := by
      rw [pow_one, div_mul_div_comm, mul_comm (x i), mul_div_mul_right _ _ hi]
    rw [h]
    exact Algebra.subset_adjoin ⟨t, rfl⟩
  | algebraMap r => exact ⟨0, by simpa using Subalgebra.algebraMap_mem _ r⟩
  | add a b _ _ ha hb =>
    obtain ⟨d, hd⟩ := ha
    obtain ⟨e, he⟩ := hb
    refine ⟨d + e, ?_⟩
    rw [mul_add]
    exact Subalgebra.add_mem _ (mono _ d _ (by omega) hd) (mono _ e _ (by omega) he)
  | mul a b _ _ ha hb =>
    obtain ⟨d, hd⟩ := ha
    obtain ⟨e, he⟩ := hb
    refine ⟨d + e, ?_⟩
    have h : (x i / x j) ^ (d + e) * (a * b) = ((x i / x j) ^ d * a) * ((x i / x j) ^ e * b) := by
      ring
    rw [h]
    exact Subalgebra.mul_mem _ hd he

open PositivityTheory.Xgn.HodgeDualOverlap in
theorem PositivityTheory.Xgn.hodge_dual_lattice_overlap : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (ι : Type) (x : ι → Ω) (r : ℕ)
    (L : ι → AddSubgroup (Fin r → Ω)),
    (∀ c, ∀ a ∈ chartRing O x c, ∀ e ∈ L c, a • e ∈ L c) →
    (∀ i j, x i ≠ 0 → x j ≠ 0 → ∀ e ∈ L i, ∃ m : ℕ, (x i / x j) ^ m • e ∈ L j) →
    (∀ c, x c ≠ 0 → ∃ (n : ℕ) (s : Fin n → Fin r → Ω), (∀ k, s k ∈ L c) ∧
      ∀ e ∈ L c, ∃ a : Fin n → Ω, (∀ k, a k ∈ chartRing O x c) ∧ e = ∑ k, a k • s k) →
    ∀ i j, x i ≠ 0 → x j ≠ 0 → ∀ e ∈ dotDual (chartRing O x i) (L i),
      ∃ m : ℕ, (x i / x j) ^ m • e ∈ dotDual (chartRing O x j) (L j) := by
  intro O _ Ω _ _ ι x r L _ h2 h3 i j hi hj e he
  rw [mem_dotDual] at he
  have hq : x i / x j ∈ chartRing O x j := Algebra.subset_adjoin ⟨i, rfl⟩
  obtain ⟨n, s, hs, hgen⟩ := h3 j hj
  have hk : ∀ k, ∃ m : ℕ, (x i / x j) ^ m * (s k ⬝ᵥ e) ∈ chartRing O x j := by
    intro k
    obtain ⟨a, ha⟩ := h2 j i hj hi (s k) (hs k)
    have hmem := he _ ha
    rw [smul_dotProduct, smul_eq_mul] at hmem
    obtain ⟨d, hd⟩ := exists_div_pow_mul_mem_chartRing x i j hi _ hmem
    refine ⟨d, ?_⟩
    have hc1 : x i / x j * (x j / x i) = 1 := by field_simp
    have hc : (x i / x j) ^ a * (x j / x i) ^ a = 1 := by rw [← mul_pow, hc1, one_pow]
    have h : (x i / x j) ^ d * (s k ⬝ᵥ e) =
        (x i / x j) ^ a * ((x i / x j) ^ d * ((x j / x i) ^ a * (s k ⬝ᵥ e))) := by
      linear_combination (-((x i / x j) ^ d * (s k ⬝ᵥ e))) * hc
    rw [h]
    exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hq _) hd
  choose m hm using hk
  refine ⟨∑ k, m k, ?_⟩
  rw [mem_dotDual]
  intro l hl
  obtain ⟨c, hc, rfl⟩ := hgen l hl
  rw [sum_dotProduct]
  refine Subalgebra.sum_mem _ (fun k _ => ?_)
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  refine Subalgebra.mul_mem _ (hc k) ?_
  have hle : m k ≤ ∑ k, m k := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hle
  rw [ht, pow_add, mul_comm ((x i / x j) ^ m k), mul_assoc]
  exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hq _) (hm k)
