import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeDivisorDegree.MonicFintype

open Polynomial Finset

noncomputable section

namespace PI.SqfDivDeg.W

open Classical

def rts {g : ℕ} [Fact g.Prime] (f : (ZMod g)[X]) : Finset (ZMod g) :=
  univ.filter (fun c => f.IsRoot c)

theorem rt_one (g : ℕ) [Fact g.Prime] : Rt g 1 = Mon g 1 := by
  unfold Rt
  apply Finset.filter_true_of_mem
  intro p hp
  rw [mem_Mon] at hp
  exact exists_root_of_degree_eq_one
    (by rw [degree_eq_natDegree hp.1.ne_zero, hp.2, Nat.cast_one])

theorem card_fib_ge {g : ℕ} [Fact g.Prime] (n : ℕ) (c : ZMod g) :
    g ^ n ≤ ((Mon g (n + 1)).filter (fun f => f.IsRoot c)).card := by
  rw [← card_Mon g n]
  apply Finset.card_le_card_of_injOn (fun h => (X - C c) * h)
  · intro h hh
    have hh' : h ∈ Mon g n := by simpa using hh
    rw [mem_Mon] at hh'
    have : (X - C c) * h ∈ (Mon g (n + 1)).filter (fun f => f.IsRoot c) := by
      rw [Finset.mem_filter, mem_Mon]
      refine ⟨⟨(monic_X_sub_C c).mul hh'.1, ?_⟩, ?_⟩
      · rw [(monic_X_sub_C c).natDegree_mul hh'.1, natDegree_X_sub_C, hh'.2]
        ring
      · simp [IsRoot]
    simpa using this
  · intro h1 _ h2 _ e
    exact mul_left_cancel₀ (X_sub_C_ne_zero c) e

theorem decomp2 {g : ℕ} [Fact g.Prime] {f : (ZMod g)[X]} {c d : ZMod g} (hcd : c ≠ d)
    (hc : f.IsRoot c) (hd : f.IsRoot d) :
    (X - C c) * ((X - C d) * ((f /ₘ (X - C c)) /ₘ (X - C d))) = f := by
  have h1 := mul_divByMonic_eq_iff_isRoot.mpr hc
  have hd1 : (f /ₘ (X - C c)).IsRoot d := by
    rw [← h1] at hd
    simp only [IsRoot, eval_mul, eval_sub, eval_X, eval_C, mul_eq_zero] at hd
    rcases hd with hd | hd
    · exact absurd (sub_eq_zero.mp hd).symm hcd
    · exact hd
  rw [mul_divByMonic_eq_iff_isRoot.mpr hd1, h1]

theorem card_monic_two_roots_le {g : ℕ} [Fact g.Prime] (n : ℕ) (c d : ZMod g) (hcd : c ≠ d) :
    ((Mon g (n + 2)).filter (fun f => f.IsRoot c ∧ f.IsRoot d)).card ≤ g ^ n := by
  rw [← card_Mon g n]
  apply Finset.card_le_card_of_injOn (fun f => (f /ₘ (X - C c)) /ₘ (X - C d))
  · intro f hf
    have hf' : f ∈ (Mon g (n + 2)).filter (fun f => f.IsRoot c ∧ f.IsRoot d) := by simpa using hf
    rw [Finset.mem_filter, mem_Mon] at hf'
    obtain ⟨⟨hm, hn⟩, hc, hd⟩ := hf'
    have e := decomp2 hcd hc hd
    set q := (f /ₘ (X - C c)) /ₘ (X - C d)
    have hm1 : ((X - C d) * q).Monic :=
      (monic_X_sub_C c).of_mul_monic_left (by rw [e]; exact hm)
    have hm2 : q.Monic := (monic_X_sub_C d).of_mul_monic_left hm1
    have hq : q ∈ Mon g n := by
      rw [mem_Mon]
      refine ⟨hm2, ?_⟩
      have := congrArg natDegree e
      rw [(monic_X_sub_C c).natDegree_mul hm1, (monic_X_sub_C d).natDegree_mul hm2,
        natDegree_X_sub_C, natDegree_X_sub_C, hn] at this
      omega
    simpa using hq
  · intro f1 hf1 f2 hf2 e
    have hf1' : f1 ∈ (Mon g (n + 2)).filter (fun f => f.IsRoot c ∧ f.IsRoot d) := by simpa using hf1
    have hf2' : f2 ∈ (Mon g (n + 2)).filter (fun f => f.IsRoot c ∧ f.IsRoot d) := by simpa using hf2
    rw [Finset.mem_filter] at hf1' hf2'
    have e1 := decomp2 hcd hf1'.2.1 hf1'.2.2
    have e2 := decomp2 hcd hf2'.2.1 hf2'.2.2
    simp only at e
    rw [← e1, ← e2, e]

theorem pt (k : ℕ) : 2 * k ≤ (k * k - k) + 2 * (if k = 0 then 0 else 1) := by
  match k with
  | 0 => simp
  | 1 => simp
  | k + 2 =>
    have h : (k + 2) * (k + 2) - (k + 2) = (k + 2) * (k + 1) := by
      rw [Nat.sub_eq_iff_eq_add (by nlinarith)]
      ring
    rw [h]
    simp
    nlinarith

theorem sum_rts {g : ℕ} [Fact g.Prime] (S : Finset (ZMod g)[X]) :
    ∑ f ∈ S, (rts f).card = ∑ c : ZMod g, (S.filter (fun f => f.IsRoot c)).card := by
  simp only [rts, Finset.card_filter]
  exact Finset.sum_comm

theorem sum_offDiag {g : ℕ} [Fact g.Prime] (S : Finset (ZMod g)[X]) :
    ∑ f ∈ S, (rts f).offDiag.card =
      ∑ x ∈ (univ : Finset (ZMod g)).offDiag,
        (S.filter (fun f => f.IsRoot x.1 ∧ f.IsRoot x.2)).card := by
  have hs : ∀ f : (ZMod g)[X], (rts f).offDiag =
      (univ : Finset (ZMod g)).offDiag.filter (fun x => f.IsRoot x.1 ∧ f.IsRoot x.2) := by
    intro f
    ext x
    simp only [rts, Finset.mem_offDiag, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  simp only [hs, Finset.card_filter]
  exact Finset.sum_comm

theorem card_Rt_eq {g : ℕ} [Fact g.Prime] (n : ℕ) :
    (Rt g n).card = ∑ f ∈ Mon g n, (if (rts f).card = 0 then 0 else 1) := by
  rw [Rt, Finset.card_filter]
  refine Finset.sum_congr rfl (fun f _ => ?_)
  have e : (∃ x, f.IsRoot x) ↔ (rts f).card ≠ 0 := by
    rw [Finset.card_ne_zero]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, by simp only [rts, Finset.mem_filter, Finset.mem_univ, true_and]; exact hx⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, by simp only [rts, Finset.mem_filter, Finset.mem_univ, true_and] at hx; exact hx⟩
  by_cases h : (rts f).card = 0
  · have : ¬ ∃ x, f.IsRoot x := fun hx => e.mp hx h
    rw [if_neg this, if_pos h]
  · rw [if_pos (e.mpr h), if_neg h]

theorem rootDense : RootDense := by
  intro g _ n hn
  obtain rfl | hn2 : n = 1 ∨ 2 ≤ n := by omega
  · rw [rt_one, card_Mon]
    omega
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hpt : ∑ f ∈ Mon g (m + 2), 2 * (rts f).card ≤
      ∑ f ∈ Mon g (m + 2), ((rts f).offDiag.card + 2 * (if (rts f).card = 0 then 0 else 1)) := by
    refine Finset.sum_le_sum (fun f _ => ?_)
    rw [Finset.offDiag_card]
    exact pt _
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← card_Rt_eq] at hpt
  have h1 : g * g ^ (m + 1) ≤ ∑ f ∈ Mon g (m + 2), (rts f).card := by
    rw [sum_rts]
    have := Finset.card_nsmul_le_sum (univ : Finset (ZMod g))
      (fun c => ((Mon g (m + 1 + 1)).filter (fun f => f.IsRoot c)).card) (g ^ (m + 1))
      (fun c _ => card_fib_ge (m + 1) c)
    simpa [ZMod.card] using this
  have h2 : ∑ f ∈ Mon g (m + 2), (rts f).offDiag.card ≤ (g * g - g) * g ^ m := by
    rw [sum_offDiag]
    have := Finset.sum_le_card_nsmul ((univ : Finset (ZMod g)).offDiag)
      (fun x => ((Mon g (m + 2)).filter (fun f => f.IsRoot x.1 ∧ f.IsRoot x.2)).card) (g ^ m)
      (fun x hx => card_monic_two_roots_le m x.1 x.2 (Finset.mem_offDiag.mp hx).2.2)
    simpa [Finset.offDiag_card, ZMod.card] using this
  have hB : (g * g - g) * g ^ m ≤ g * g * g ^ m := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have eA : g ^ (m + 2) = g * g * g ^ m := by ring
  have eA' : g * g ^ (m + 1) = g * g * g ^ m := by ring
  rw [eA]
  rw [eA'] at h1
  omega

end PI.SqfDivDeg.W
