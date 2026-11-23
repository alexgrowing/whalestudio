import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSumRowCol
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

namespace GlobalTheory.RootEx.UnipPow

theorem pow_dvd_choose {q : ℕ} (hq : q.Prime) (m : ℕ) {i : ℕ} (hi : i ≠ 0) :
    q ^ (m - i) ∣ (q ^ m).choose i := by
  have := Fact.mk hq
  rcases Nat.eq_zero_or_pos ((q ^ m).choose i) with h0 | hpos
  · rw [h0]
    exact dvd_zero _
  have hdvd : q ^ m ∣ (q ^ m).choose i * i := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hi
    obtain ⟨N, hN⟩ := Nat.exists_eq_add_one_of_ne_zero (pow_ne_zero m hq.ne_zero)
    rw [hN]
    exact ⟨N.choose j, (Nat.add_one_mul_choose_eq N j).symm⟩
  have hv : m ≤ padicValNat q ((q ^ m).choose i) + padicValNat q i := by
    rw [← padicValNat.mul hpos.ne' hi]
    exact (padicValNat_dvd_iff_le (mul_ne_zero hpos.ne' hi)).mp hdvd
  have hi' : padicValNat q i < i := (padicValNat_le_nat_log i).trans_lt (Nat.log_lt_self q hi)
  exact (padicValNat_dvd_iff_le hpos.ne').mpr (by omega)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem valuation_resCard_lt_one : valuation k (resCard k : k) < 1 := by
  have hres : IsLocalRing.residue 𝒪[k] (resCard k : 𝒪[k]) = 0 := by
    let := Fintype.ofFinite 𝓀[k]
    rw [map_natCast, resCard, Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero _
  have hnu : ¬ IsUnit (resCard k : 𝒪[k]) := by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hres
    exact hres
  have hlt := (Valuation.Integer.not_isUnit_iff_valuation_lt_one (v := valuation k)).mp hnu
  simpa using hlt

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem valuation_natCast_le_one (j : ℕ) : valuation k (j : k) ≤ 1 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.cast_succ]
    exact ((valuation k).map_add _ _).trans (max_le ih (by simp))

theorem tendsto_choose (hq : (resCard k).Prime) {i : ℕ} (hi : i ≠ 0) :
    Filter.Tendsto (fun m : ℕ => (((resCard k ^ m).choose i : ℕ) : k)) Filter.atTop (𝓝 0) := by
  rw [(IsValuativeTopology.hasBasis_nhds_zero k).tendsto_right_iff]
  intro γ _
  have hq1 := valuation_resCard_lt_one (k := k)
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hq1 γ
  rw [Filter.eventually_atTop]
  refine ⟨n + i, fun m hm => ?_⟩
  obtain ⟨t, ht⟩ := pow_dvd_choose hq m hi
  show valuation k (((resCard k ^ m).choose i : ℕ) : k) < γ
  rw [ht, Nat.cast_mul, map_mul, Nat.cast_pow, map_pow]
  calc valuation k (resCard k : k) ^ (m - i) * valuation k (t : k)
      ≤ valuation k (resCard k : k) ^ (m - i) := mul_le_of_le_one_right' (valuation_natCast_le_one t)
    _ ≤ valuation k (resCard k : k) ^ n := pow_le_pow_right_of_le_one' hq1.le (by omega)
    _ < γ := hn

theorem add_one_pow_eq {R : Type} [Ring R] {a : R} {d : ℕ} (ha : a ^ d = 0) (M : ℕ) :
    (a + 1) ^ M = ∑ i ∈ Finset.range d, (M.choose i) • a ^ i := by
  rw [(Commute.one_right a).add_pow]
  simp only [one_pow, mul_one]
  have key : ∀ s : Finset ℕ, ∑ i ∈ s, a ^ i * (M.choose i : R) = ∑ i ∈ s, M.choose i • a ^ i :=
    fun s => Finset.sum_congr rfl fun i _ => by rw [nsmul_eq_mul]; exact (Nat.cast_comm _ _).symm
  rw [key]
  calc ∑ i ∈ Finset.range (M + 1), M.choose i • a ^ i
      = ∑ i ∈ Finset.range (M + 1 + d), M.choose i • a ^ i := by
        refine Finset.sum_subset (Finset.range_mono (by omega)) fun i hi hi' => ?_
        rw [Finset.mem_range] at hi'
        rw [Nat.choose_eq_zero_of_lt (by omega : M < i), zero_smul]
    _ = ∑ i ∈ Finset.range d, M.choose i • a ^ i := by
        refine (Finset.sum_subset (Finset.range_mono (by omega)) fun i hi hi' => ?_).symm
        rw [Finset.mem_range] at hi'
        rw [pow_eq_zero_of_le (by omega : d ≤ i) ha, smul_zero]

theorem tendsto_pow_of_nilpotent {ι : Type} [Fintype ι] [DecidableEq ι] (hq : (resCard k).Prime)
    {g : Matrix ι ι k} {d : ℕ} (ha : (g - 1) ^ (d + 1) = 0) :
    Filter.Tendsto (fun m : ℕ => g ^ (resCard k ^ m)) Filter.atTop (𝓝 1) := by
  have hexp : ∀ m : ℕ, g ^ (resCard k ^ m) =
      ∑ i ∈ Finset.range (d + 1), (((resCard k ^ m).choose i : ℕ) : k) • (g - 1) ^ i := by
    intro m
    have h := add_one_pow_eq ha (resCard k ^ m)
    rw [sub_add_cancel] at h
    rw [h]
    exact Finset.sum_congr rfl fun i _ => (Nat.cast_smul_eq_nsmul k _ _).symm
  have hlim := (tendsto_finsetSum (Finset.range d) fun i _ =>
    (tendsto_choose hq (Nat.succ_ne_zero i)).smul_const ((g - 1) ^ (i + 1))).add
    (tendsto_const_nhds (x := (1 : Matrix ι ι k)))
  simp only [zero_smul, Finset.sum_const_zero, zero_add] at hlim
  refine hlim.congr fun m => ?_
  rw [hexp, Finset.sum_range_succ']
  simp

theorem pow_sub_one_apply {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}
    {g : GL (n ⊕ Fin c) K} (hg : InN p g) (j : ℕ) :
    ∀ r s : n ⊕ Fin c, lev p s < lev p r + j →
      (((g : Matrix (n ⊕ Fin c) (n ⊕ Fin c) K) - 1) ^ j) r s = 0 := by
  induction j with
  | zero =>
    intro r s h
    rw [pow_zero, Matrix.one_apply_ne (by rintro rfl; omega)]
  | succ j ih =>
    intro r s h
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun t _ => ?_
    by_cases ht : lev p t < lev p r + j
    · rw [ih r t ht, zero_mul]
    · rw [Matrix.sub_apply, hg t s (by omega), sub_self, mul_zero]

theorem pow_sub_one_eq_zero {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}
    {g : GL (n ⊕ Fin c) K} (hg : InN p g) :
    ((g : Matrix (n ⊕ Fin c) (n ⊕ Fin c) K) - 1) ^ (c + p + 1) = 0 := by
  have hb : ∀ t : n ⊕ Fin c, lev p t ≤ c + p := by
    rintro (t | t)
    · show p ≤ c + p
      omega
    · show t.val + 1 ≤ c + p
      have := t.isLt
      omega
  ext r s
  rw [Matrix.zero_apply]
  exact pow_sub_one_apply hg _ r s (by have := hb s; omega)

theorem inN_of_mem {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}
    {g : GL (n ⊕ Fin c) K} (hg : g ∈ N K n c p) : InN p g := by
  have hle : N K n c p ≤ GlobalTheory.RootEx.Model.Nsub K n c p :=
    (Subgroup.closure_le _).mpr fun x hx => hx
  exact hle hg

theorem exists_pow_mem_nhds (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ)
    (hq : (resCard k).Prime) :
    ∀ u ∈ N k n c p, ∀ U ∈ 𝓝 (1 : GL (n ⊕ Fin c) k), ∃ m : ℕ, u ^ (resCard k ^ m) ∈ U := by
  intro u hu U hU
  have h1 := tendsto_pow_of_nilpotent (k := k) hq (pow_sub_one_eq_zero (inN_of_mem hu))
  have h2 := tendsto_pow_of_nilpotent (k := k) hq (pow_sub_one_eq_zero (inN_of_mem (inv_mem hu)))
  have hA : Filter.Tendsto (fun m : ℕ => ((u ^ (resCard k ^ m) : GL (n ⊕ Fin c) k) :
      Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)) Filter.atTop (𝓝 1) :=
    h1.congr fun m => (Units.val_pow_eq_pow_val _ _).symm
  have hB : Filter.Tendsto (fun m : ℕ => (((u ^ (resCard k ^ m))⁻¹ : GL (n ⊕ Fin c) k) :
      Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)) Filter.atTop (𝓝 1) :=
    h2.congr fun m => by rw [← inv_pow, Units.val_pow_eq_pow_val]
  have hT : Filter.Tendsto (fun m : ℕ => u ^ (resCard k ^ m)) Filter.atTop (𝓝 1) := by
    rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
    have hP := hA.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp hB)
    simpa [Function.comp_def] using hP
  exact (hT.eventually_mem hU).exists

end GlobalTheory.RootEx.UnipPow
