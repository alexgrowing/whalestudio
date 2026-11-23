import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DiscriminantNonzeroOfInjectiveTops

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem late_vectors_distinct_tops : LateVectorsDistinctLeadingTerms := by
  intro p n' r K _ _ _ X hX j x hx
  obtain ⟨-, -, -, hnext, hTT, -⟩ := hX.valid
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hn : (0 : ℤ) < n' := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n')
  have hstep : ∀ t : ℤ, ∀ i < r, ∀ i' < r, X.F.fr t i < X.F.fr (t + 1) i' := by
    intro t i hi i' hi'
    calc X.F.fr t i ≤ X.F.fr t (r - 1) := bk_fr_le hX.valid t i (r - 1) (by omega) (by omega)
      _ < X.F.fr (t + 1) 0 := hnext t
      _ ≤ X.F.fr (t + 1) i' := fr_zero_le hX.valid (t + 1) i' hi'
  have hlt' : ∀ t : ℤ, ∀ k : ℕ, ∀ i < r, ∀ i' < r, X.F.fr t i < X.F.fr (t + 1 + k) i' := by
    intro t k
    induction k with
    | zero =>
      intro i hi i' hi'
      simpa using hstep t i hi i' hi'
    | succ k ih =>
      intro i hi i' hi'
      rw [show t + 1 + ((k + 1 : ℕ) : ℤ) = t + 1 + k + 1 by push_cast; ring]
      exact (ih i hi 0 hr).trans (hstep _ 0 hr i' hi')
  have hlt : ∀ t t' : ℤ, t < t' → ∀ i < r, ∀ i' < r, X.F.fr t i < X.F.fr t' i' := by
    intro t t' htt i hi i' hi'
    obtain ⟨k, hk⟩ : ∃ k : ℕ, t' = t + 1 + k := ⟨(t' - t - 1).toNat, by omega⟩
    rw [hk]
    exact hlt' t k i hi i' hi'
  have hinjfr : ∀ t t' : ℤ, ∀ i < r, ∀ i' < r, X.F.fr t i = X.F.fr t' i' → t = t' ∧ i = i' := by
    intro t t' i hi i' hi' h
    rcases lt_trichotomy t t' with h1 | rfl | h1
    · exact absurd h (hlt t t' h1 i hi i' hi').ne
    · refine ⟨rfl, ?_⟩
      rcases lt_trichotomy i i' with h2 | h2 | h2
      · exact absurd h (bk_fr_lt hX.valid t i i' h2 hi').ne
      · exact h2
      · exact absurd h.symm (bk_fr_lt hX.valid t i' i h2 hi).ne
    · exact absurd h.symm (hlt t' t h1 i' hi' i hi).ne
  rw [mem_late] at hx
  obtain ⟨-, hxW⟩ := hx
  simp only [Frames.IsW, not_le] at hxW
  obtain ⟨S, hS⟩ : ∃ S : Finset ℤ, S = {z ∈ X.F.letters j | Even z ∧ z < x} := ⟨_, rfl⟩
  have hmem : ∀ z, z ∈ evL X.F j x ↔ z ∈ S := fun z => by
    rw [hS]
    exact Finset.mem_sort _
  have hsort : (evL X.F j x).Pairwise (· < ·) := by
    rw [evL, ← hS]
    exact ((Finset.pairwise_sort S _).and (Finset.sort_nodup S _)).imp (fun h => lt_of_le_of_ne h.1 h.2)
  have hlen : (evL X.F j x).length = S.card := by
    rw [evL, ← hS]
    exact Finset.length_sort _
  have hfrS : ∀ t : ℤ, ∀ i < r, X.F.fr (j - 1) 0 ≤ X.F.fr t i → X.F.fr t i ≤ X.F.fr j (r - 1) →
      X.F.fr t i < x → X.F.fr t i ∈ S := by
    intro t i hi h1 h2 h3
    rw [hS]
    simp only [Finset.mem_filter, Frames.letters, Finset.mem_Icc]
    exact ⟨⟨⟨h1, h2⟩, (hTT t i hi).1⟩, (hTT t i hi).2, h3⟩
  have hSlo : ∀ z ∈ S, X.F.fr (j - 1) 0 ≤ z ∧ z ≤ X.F.fr j (r - 1) ∧ z < x := by
    intro z hz
    rw [hS, Finset.mem_filter] at hz
    have hb := mem_letters_bounds hz.1
    exact ⟨hb.1, hb.2.1, hz.2.2⟩
  have hlenr : r ≤ S.card := by
    have hsub : (Finset.range r).image (fun i => X.F.fr (j - 1) i) ⊆ S := by
      intro z hz
      simp only [Finset.mem_image, Finset.mem_range] at hz
      obtain ⟨i, hi, rfl⟩ := hz
      have hA : X.F.fr (j - 1) i ≤ X.F.fr (j - 1) (r - 1) :=
        bk_fr_le hX.valid _ i (r - 1) (by omega) (by omega)
      have hB : X.F.fr (j - 1) i < X.F.fr j (r - 1) := hlt (j - 1) j (by omega) i hi (r - 1) (by omega)
      exact hfrS _ i hi (fr_zero_le hX.valid _ i hi) hB.le (lt_of_le_of_lt hA hxW)
    have hinj' : Set.InjOn (fun i => X.F.fr (j - 1) i) ↑(Finset.range r) := by
      intro a ha b hb h
      simp only [Finset.coe_range, Set.mem_Iio] at ha hb
      exact (hinjfr _ _ a ha b hb h).2
    have hc := Finset.card_le_card hsub
    rw [Finset.card_image_of_injOn hinj', Finset.card_range] at hc
    exact hc
  simp only [row_eq]
  generalize evL X.F j x = l at hmem hsort hlen ⊢
  have hNr : r ≤ l.length := hlen ▸ hlenr
  have hget : ∀ k (hk : k < l.length), l.getD k 0 = l[k] := fun k hk => List.getD_eq_getElem _ _ hk
  have hpw := List.pairwise_iff_getElem.mp hsort
  have hm : l.length - r < l.length := by omega
  have hinS : ∀ k, k < l.length → l.getD k 0 ∈ S := by
    intro k hk
    rw [hget k hk]
    exact (hmem _).1 (List.getElem_mem _)
  have hbound : ∀ k, l.length - r ≤ k → k < l.length →
      l.getD (l.length - r) 0 ≤ l.getD k 0 ∧ l.getD k 0 < l.getD (l.length - r) 0 + n' := by
    intro k hk1 hk2
    refine ⟨?_, ?_⟩
    · rcases eq_or_lt_of_le hk1 with h | h
      · rw [h]
      · rw [hget _ hm, hget _ hk2]
        exact (hpw _ _ hm hk2 h).le
    · by_contra hz
      push_neg at hz
      have hy1S := hinS _ hm
      have hzS := hinS _ hk2
      obtain ⟨hy1lo, -, -⟩ := hSlo _ hy1S
      obtain ⟨-, hzhi, hzx⟩ := hSlo _ hzS
      obtain ⟨y1, hy1⟩ : ∃ y1, y1 = l.getD (l.length - r) 0 := ⟨_, rfl⟩
      obtain ⟨z, hzdef⟩ : ∃ z, z = l.getD k 0 := ⟨_, rfl⟩
      rw [← hy1, ← hzdef] at hz
      rw [← hy1] at hy1lo hy1S
      rw [← hzdef] at hzhi hzx hzS
      let w : ℕ → ℤ := fun i => X.F.fr (0 + (-((X.F.fr 0 i - y1) / n')) * X.F.J) i
      have hwr : ∀ i < r, y1 ≤ w i ∧ w i < y1 + n' := by
        intro i hi
        have hw : w i = X.F.fr 0 i + (-((X.F.fr 0 i - y1) / n')) * n' :=
          fr_period hX.valid 0 i (-((X.F.fr 0 i - y1) / n'))
        have e1 := Int.mul_ediv_add_emod (X.F.fr 0 i - y1) (n' : ℤ)
        have e2 := Int.emod_nonneg (X.F.fr 0 i - y1) (ne_of_gt hn)
        have e3 := Int.emod_lt_of_pos (X.F.fr 0 i - y1) hn
        have e4 : (-((X.F.fr 0 i - y1) / n')) * (n' : ℤ) = -((n' : ℤ) * ((X.F.fr 0 i - y1) / n')) := by ring
        constructor <;> linarith
      obtain ⟨T, hT⟩ : ∃ T : Finset ℤ, T = S.filter (fun s => y1 ≤ s) := ⟨_, rfl⟩
      have hTcard : T.card ≤ r := by
        have hsub : T ⊆ (Finset.Ico (l.length - r) l.length).image (fun k => l.getD k 0) := by
          intro s hs
          rw [hT, Finset.mem_filter] at hs
          obtain ⟨k', hk', rfl⟩ := List.getElem_of_mem ((hmem _).2 hs.1)
          refine Finset.mem_image.2 ⟨k', Finset.mem_Ico.2 ⟨?_, hk'⟩, hget k' hk'⟩
          by_contra hlt2
          push_neg at hlt2
          have h3 := hpw k' _ hk' hm hlt2
          have h2 := hs.2
          rw [hy1, hget _ hm] at h2
          exact absurd h2 (not_le.2 h3)
        have := (Finset.card_le_card hsub).trans Finset.card_image_le
        rw [Nat.card_Ico] at this
        omega
      have hwinj : Set.InjOn w ↑(Finset.range r) := by
        intro a ha b hb h
        simp only [Finset.coe_range, Set.mem_Iio] at ha hb
        exact (hinjfr _ _ a ha b hb h).2
      have hznot : z ∉ (Finset.range r).image w := by
        intro hzin
        simp only [Finset.mem_image, Finset.mem_range] at hzin
        obtain ⟨i, hi, hwi⟩ := hzin
        have := (hwr i hi).2
        linarith
      have hUsub : insert z ((Finset.range r).image w) ⊆ T := by
        intro s hs
        rw [Finset.mem_insert] at hs
        rw [hT, Finset.mem_filter]
        rcases hs with rfl | hs
        · exact ⟨hzS, by linarith⟩
        · simp only [Finset.mem_image, Finset.mem_range] at hs
          obtain ⟨i, hi, rfl⟩ := hs
          obtain ⟨hw1, hw2⟩ := hwr i hi
          exact ⟨hfrS _ i hi (by linarith) (by linarith) (by linarith), hw1⟩
      have hc := Finset.card_le_card hUsub
      rw [Finset.card_insert_of_notMem hznot, Finset.card_image_of_injOn hwinj, Finset.card_range] at hc
      omega
  intro a b hab
  simp only at hab
  have ha := hbound (l.length - r + a) (by omega) (by omega)
  have hb := hbound (l.length - r + b) (by omega) (by omega)
  have he := posOf_injOn (l.getD (l.length - r) 0 - 1)
    (show l.getD (l.length - r + a) 0 ∈ Set.Ioc _ _ from ⟨by linarith [ha.1], by linarith [ha.2]⟩)
    (show l.getD (l.length - r + b) 0 ∈ Set.Ioc _ _ from ⟨by linarith [hb.1], by linarith [hb.2]⟩) hab
  have hia : l.length - r + (a : ℕ) < l.length := by omega
  have hib : l.length - r + (b : ℕ) < l.length := by omega
  rw [hget _ hia, hget _ hib] at he
  apply Fin.ext
  rcases lt_trichotomy (l.length - r + (a : ℕ)) (l.length - r + (b : ℕ)) with h | h | h
  · exact absurd he (hpw _ _ hia hib h).ne
  · omega
  · exact absurd he.symm (hpw _ _ hib hia h).ne

end Formalism.MainNotions.SelectionLemmas.Pf
