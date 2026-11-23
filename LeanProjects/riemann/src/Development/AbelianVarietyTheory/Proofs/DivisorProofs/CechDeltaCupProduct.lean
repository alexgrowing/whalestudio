import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift
open GlobalTheory GlobalTheory.DI

set_option autoImplicit false

namespace GlobalTheory.DI

section CupDelta

variable {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E]

theorem sum_alt_filter_lt_le (F : Finset ι → E) (u : Finset ι) :
    ∑ j ∈ u, (-1 : ℤ) ^ (u.filter (· < j)).card • (F (u.filter (· < j)) + F (u.filter (· ≤ j))) =
      F ∅ - (-1 : ℤ) ^ u.card • F u := by
  induction u using Finset.induction_on_max with
  | empty => simp
  | insert m u hm ih =>
    have hmu : m ∉ u := fun h => lt_irrefl m (hm m h)
    rw [Finset.sum_insert hmu]
    rw [Finset.sum_congr rfl (g := fun j => (-1 : ℤ) ^ (u.filter (· < j)).card •
        (F (u.filter (· < j)) + F (u.filter (· ≤ j)))) (fun j hj => by
      rw [Finset.filter_insert, if_neg (not_lt.2 (hm j hj).le), Finset.filter_insert,
        if_neg (not_le.2 (hm j hj))]), ih]
    have e1 : (insert m u).filter (· < m) = u := by
      ext x; simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hx, hxm⟩
        · exact absurd hxm (lt_irrefl _)
        · exact hx
      · intro hx; exact ⟨Or.inr hx, hm x hx⟩
    have e2 : (insert m u).filter (· ≤ m) = insert m u := by
      ext x; simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · exact fun h => h.1
      · rintro (rfl | hx)
        · exact ⟨Or.inl rfl, le_rfl⟩
        · exact ⟨Or.inr hx, (hm x hx).le⟩
    rw [e1, e2, Finset.card_insert_of_notMem hmu, pow_succ, smul_add, mul_neg_one, neg_smul]
    abel

theorem delta_cup_eq : ∀ {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E]
    (Φ : E →+ (Finset ι → E)) (c : Finset ι → E), (∀ x, Φ x ∅ = 0) → c ∅ = 0 → ∀ u,
    delta (cup Φ c) u = cup Φ (delta c) u + ∑ j ∈ u, (-1 : ℤ) ^ (u.filter (· < j)).card •
      delta (Φ (c (u.filter (· ≤ j)))) (u.filter (j ≤ ·)) := by
  intro ι _ E _ Φ c hΦ hc u

  have sL : ∀ {i j : ι}, i < j → cubeSign u i = cubeSign (u.filter (· ≤ j)) i := by
    intro i j hij
    have : (u.filter (· ≤ j)).filter (· < i) = u.filter (· < i) := by
      ext x; simp only [Finset.mem_filter]; grind
    unfold cubeSign; rw [this]
  have sR : ∀ {i j : ι}, j < i → cubeSign u i =
      (-1 : ℤ) ^ (u.filter (· < j)).card * cubeSign (u.filter (j ≤ ·)) i := by
    intro i j hji
    have hd : Disjoint (u.filter (· < j)) ((u.filter (j ≤ ·)).filter (· < i)) := by
      rw [Finset.disjoint_left]; intro x h1 h2
      simp only [Finset.mem_filter] at h1 h2
      exact absurd h1.2 (not_lt.2 h2.1.2)
    have : u.filter (· < i) = u.filter (· < j) ∪ (u.filter (j ≤ ·)).filter (· < i) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_union]; grind
    unfold cubeSign; rw [← pow_add, ← Finset.card_union_of_disjoint hd, this]

  have hL : delta (cup Φ c) u = ∑ j ∈ u, ∑ i ∈ u.erase j,
      cubeSign u i • Φ (c ((u.erase i).filter (· ≤ j))) ((u.erase i).filter (j ≤ ·)) := by
    simp only [delta, cup, Finset.smul_sum]
    exact Finset.sum_comm' (fun i j => by simp only [Finset.mem_erase]; tauto)

  have key : ∀ j ∈ u, Φ (delta c (u.filter (· ≤ j))) (u.filter (j ≤ ·)) +
      (-1 : ℤ) ^ (u.filter (· < j)).card • delta (Φ (c (u.filter (· ≤ j)))) (u.filter (j ≤ ·)) =
      ∑ i ∈ u.erase j,
        cubeSign u i • Φ (c ((u.erase i).filter (· ≤ j))) ((u.erase i).filter (j ≤ ·)) +
      (-1 : ℤ) ^ (u.filter (· < j)).card • (Φ (c (u.filter (· < j))) (u.filter (j ≤ ·)) +
        Φ (c (u.filter (· ≤ j))) (u.filter (j < ·))) := by
    intro j hj
    have eL : (u.erase j).filter (· < j) = u.filter (· < j) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_erase]; grind
    have eG : (u.erase j).filter (fun x => ¬ x < j) = u.filter (j < ·) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_erase]; grind
    have eLeL : (u.filter (· ≤ j)).filter (· < j) = u.filter (· < j) := by
      ext x; simp only [Finset.mem_filter]; grind
    have eLeJ : (u.filter (· ≤ j)).filter (fun x => ¬ x < j) = {j} := by
      ext x; simp only [Finset.mem_filter, Finset.mem_singleton]; grind
    have eGeG : (u.filter (j ≤ ·)).filter (j < ·) = u.filter (j < ·) := by
      ext x; simp only [Finset.mem_filter]; grind
    have eGeJ : (u.filter (j ≤ ·)).filter (fun x => ¬ j < x) = {j} := by
      ext x; simp only [Finset.mem_filter, Finset.mem_singleton]; grind
    have eLeE : (u.filter (· ≤ j)).erase j = u.filter (· < j) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_erase]; grind
    have eGeE : (u.filter (j ≤ ·)).erase j = u.filter (j < ·) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_erase]; grind

    rw [← Finset.sum_filter_add_sum_filter_not (u.erase j) (· < j), eL, eG]

    have h1 : Φ (delta c (u.filter (· ≤ j))) (u.filter (j ≤ ·)) =
        ∑ i ∈ u.filter (· < j), cubeSign (u.filter (· ≤ j)) i •
          Φ (c ((u.filter (· ≤ j)).erase i)) (u.filter (j ≤ ·)) +
        (-1 : ℤ) ^ (u.filter (· < j)).card • Φ (c (u.filter (· < j))) (u.filter (j ≤ ·)) := by
      simp only [delta, map_sum, map_zsmul, Finset.sum_apply, Pi.smul_apply]
      rw [← Finset.sum_filter_add_sum_filter_not (u.filter (· ≤ j)) (· < j), eLeL, eLeJ,
        Finset.sum_singleton, eLeE]
      congr 2
      unfold cubeSign; rw [eLeL]

    have h2 : delta (Φ (c (u.filter (· ≤ j)))) (u.filter (j ≤ ·)) =
        ∑ i ∈ u.filter (j < ·), cubeSign (u.filter (j ≤ ·)) i •
          Φ (c (u.filter (· ≤ j))) ((u.filter (j ≤ ·)).erase i) +
        Φ (c (u.filter (· ≤ j))) (u.filter (j < ·)) := by
      simp only [delta]
      rw [← Finset.sum_filter_add_sum_filter_not (u.filter (j ≤ ·)) (j < ·), eGeG, eGeJ,
        Finset.sum_singleton, eGeE, cubeSign_eq_one_of_forall_le (by simp), one_smul]
    rw [h1, h2, smul_add, Finset.smul_sum]
    have hA : ∑ i ∈ u.filter (· < j), cubeSign u i •
          Φ (c ((u.erase i).filter (· ≤ j))) ((u.erase i).filter (j ≤ ·)) =
        ∑ i ∈ u.filter (· < j), cubeSign (u.filter (· ≤ j)) i •
          Φ (c ((u.filter (· ≤ j)).erase i)) (u.filter (j ≤ ·)) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hij : i < j := (Finset.mem_filter.1 hi).2
      rw [sL hij, Finset.filter_erase, Finset.filter_erase,
        Finset.erase_eq_of_notMem (s := u.filter (j ≤ ·)) (by simp [hij])]
    have hB : ∑ i ∈ u.filter (j < ·), cubeSign u i •
          Φ (c ((u.erase i).filter (· ≤ j))) ((u.erase i).filter (j ≤ ·)) =
        ∑ i ∈ u.filter (j < ·), (-1 : ℤ) ^ (u.filter (· < j)).card •
          cubeSign (u.filter (j ≤ ·)) i • Φ (c (u.filter (· ≤ j))) ((u.filter (j ≤ ·)).erase i) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hji : j < i := (Finset.mem_filter.1 hi).2
      rw [sR hji, Finset.filter_erase, Finset.filter_erase,
        Finset.erase_eq_of_notMem (s := u.filter (· ≤ j)) (by simp [hji]), mul_smul]
    rw [hA, hB]
    simp only [smul_add]
    abel

  have tele := sum_alt_filter_lt_le (fun s => Φ (c s) (u \ s)) u
  simp only [Finset.sdiff_self, hΦ, Finset.sdiff_empty, hc, map_zero, Pi.zero_apply, smul_zero,
    sub_zero] at tele
  have hT : ∑ j ∈ u, (-1 : ℤ) ^ (u.filter (· < j)).card • (Φ (c (u.filter (· < j))) (u.filter (j ≤ ·)) +
      Φ (c (u.filter (· ≤ j))) (u.filter (j < ·))) = 0 := by
    rw [← tele]
    refine Finset.sum_congr rfl fun j _ => ?_
    have a1 : u \ u.filter (· < j) = u.filter (j ≤ ·) := by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_filter]; grind
    have a2 : u \ u.filter (· ≤ j) = u.filter (j < ·) := by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_filter]; grind
    rw [a1, a2]
  rw [hL]
  show _ = ∑ j ∈ u, Φ (delta c (u.filter (· ≤ j))) (u.filter (j ≤ ·)) + _
  rw [← Finset.sum_add_distrib, Finset.sum_congr rfl key, Finset.sum_add_distrib, hT, add_zero]

end CupDelta

end GlobalTheory.DI
