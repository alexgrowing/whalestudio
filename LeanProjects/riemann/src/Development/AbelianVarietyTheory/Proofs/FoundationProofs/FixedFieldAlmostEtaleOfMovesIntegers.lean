import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SeparatingFamilySumClosedUnderProdStatement
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

open Topology

lemma exists_lt_one_lt_pow (r : ℝ≥0) (hr : r < 1) (k : ℕ) : ∃ t : ℝ≥0, t < 1 ∧ r < t ^ k := by
  have hopen : IsOpen {t : ℝ≥0 | r < t ^ k} := isOpen_lt continuous_const (continuous_pow k)
  have hmem : {t : ℝ≥0 | r < t ^ k} ∈ 𝓝 (1 : ℝ≥0) := hopen.mem_nhds (by simpa using hr)
  obtain ⟨l, hl, hsub⟩ := exists_Ioc_subset_of_mem_nhds hmem ⟨0, zero_lt_one⟩
  obtain ⟨t, hlt, ht1⟩ := exists_between hl
  exact ⟨t, ht1, hsub ⟨hlt, ht1.le⟩⟩

lemma smul_mem_fix {L : Type} [Field L] {G : Type} [Group G] [MulSemiringAction G L]
    (N : Subgroup G) [hN : N.Normal] (g : G) {y : L} (hy : y ∈ Fix L N) : g • y ∈ Fix L N := by
  intro n
  have hc : g⁻¹ * (n : G) * g ∈ N := by
    have := hN.conj_mem (n : G) n.2 g⁻¹
    simpa using this
  have h1 : (g⁻¹ * (n : G) * g) • y = y := hy ⟨_, hc⟩
  show (n : G) • g • y = g • y
  calc (n : G) • g • y = g • ((g⁻¹ * (n : G) * g) • y) := by
        simp only [mul_smul, smul_inv_smul]
    _ = g • y := by rw [h1]

lemma fix_smul {L : Type} [Field L] {G : Type} [Group G] [MulSemiringAction G L]
    (N : Subgroup G) {y : L} (hy : y ∈ Fix L N) {σ : G} (hσ : σ ∈ N) : σ • y = y :=
  hy ⟨σ, hσ⟩

theorem almostSep_of_moves : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G]
    [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ N : Subgroup G, N.Normal →
    N.FiniteIndex → (∀ σ : G, σ ∉ N → Moves v (Fix L N) σ) → AlmostSep v N := by
  intro L _ v G _ _ hv N hN hfi hmov r hr
  classical
  haveI : Finite (G ⧸ N) := inferInstance
  letI : Fintype (G ⧸ N) := Fintype.ofFinite _
  set s : Finset (G ⧸ N) := Finset.univ.erase 1 with hs
  obtain ⟨t, ht1, hrt⟩ := exists_lt_one_lt_pow r hr s.card
  have hex : ∀ q : G ⧸ N, ∃ y : L, y ∈ Fix L N ∧ v y ≤ 1 ∧ (q ≠ 1 → t < v (q.out • y - y)) := by
    intro q
    by_cases hq : q = 1
    · exact ⟨0, zero_mem _, by simp, fun h => absurd hq h⟩
    · have hout : q.out ∉ N := by
        intro hm
        apply hq
        rw [← QuotientGroup.out_eq' q]
        exact (QuotientGroup.eq_one_iff _).2 hm
      obtain ⟨y, hyF, hyv, hyt⟩ := hmov _ hout t ht1
      exact ⟨y, hyF, hyv, fun _ => hyt⟩
  choose y hyF hyv hyt using hex
  let x : G ⧸ N → L := fun q => q.out • y q
  have hxF : ∀ q, x q ∈ Fix L N := fun q => smul_mem_fix N _ (hyF q)
  have hxv : ∀ q, v (x q) ≤ 1 := fun q => by simp only [x, hv]; exact hyv q
  obtain ⟨n, a, b, hab, hsum⟩ := GlobalTheory.T.separating_family_sum_closed_under_prod L v G (Fix L N) (G ⧸ N) s x y
    (fun j _ => ⟨hxF j, hyF j, hxv j, hyv j⟩)
  refine ⟨n, a, b, ∏ q ∈ s, (x q - y q), ?_, ?_⟩
  · refine
      { a_mem := fun i => (hab i).1
        b_mem := fun i => (hab i).2.1
        c_mem := ?_
        a_le := fun i => (hab i).2.2.1
        b_le := fun i => (hab i).2.2.2
        c_le := ?_
        sum_in := ?_
        sum_out := ?_ }
    · exact prod_mem fun q _ => sub_mem (hxF q) (hyF q)
    · rw [map_prod]
      refine Finset.prod_le_one (fun _ _ => zero_le) fun q _ => ?_
      exact (Valuation.map_sub v _ _).trans (max_le (hxv q) (hyv q))
    · intro σ hσ
      rw [hsum σ]
      refine Finset.prod_congr rfl fun q _ => ?_
      rw [fix_smul N (hyF q) hσ]
    · intro σ hσ
      rw [hsum σ]
      have hq : (σ : G ⧸ N) ∈ s := by
        rw [hs, Finset.mem_erase]
        refine ⟨?_, Finset.mem_univ _⟩
        intro h
        exact hσ ((QuotientGroup.eq_one_iff σ).1 h)
      refine Finset.prod_eq_zero hq ?_
      obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul N σ
      simp only [x]
      rw [hm, mul_smul, fix_smul N (hyF _) m.2, sub_self]
  · rw [map_prod]
    calc r < t ^ s.card := hrt
      _ = ∏ _q ∈ s, t := by rw [Finset.prod_const]
      _ ≤ ∏ q ∈ s, v (x q - y q) := by
        refine Finset.prod_le_prod (fun _ _ => zero_le) fun q hq => ?_
        exact (hyt q (Finset.ne_of_mem_erase hq)).le

end GlobalTheory.AlmostEt
