import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.NewtonSlope

theorem exists_dvd_all {S ι : Type} [CommRing S] (T : Finset ι) (hT : T.Nonempty) (r : ι → S)
    (hc : ∀ i ∈ T, ∀ j ∈ T, r i ∣ r j ∨ r j ∣ r i) :
    ∃ i₀ ∈ T, ∀ j ∈ T, r j ∣ r i₀ := by
  classical
  revert hT hc
  refine Finset.induction_on T ?_ ?_
  · intro hT
    exact absurd hT Finset.not_nonempty_empty
  · intro a s ha ih hT hc
    rcases s.eq_empty_or_nonempty with hs | hs
    · subst hs
      refine ⟨a, Finset.mem_insert_self a ∅, ?_⟩
      intro j hj
      rw [Finset.mem_insert] at hj
      rcases hj with rfl | hj
      · exact dvd_refl _
      · exact absurd hj (Finset.notMem_empty j)
    · obtain ⟨i₀, hi₀, hmax⟩ := ih hs (fun i hi j hj =>
        hc i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))
      rcases hc a (Finset.mem_insert_self a s) i₀ (Finset.mem_insert_of_mem hi₀) with h | h
      · refine ⟨i₀, Finset.mem_insert_of_mem hi₀, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact h
        · exact hmax j hj
      · refine ⟨a, Finset.mem_insert_self a s, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact dvd_refl _
        · exact (hmax j hj).trans h

theorem dich_of_dvd {S : Type} [CommRing S] {ϖ : S} (hD : Dich ϖ) {a b : S} {M : ℕ}
    (h : a ∣ ϖ ^ M) : b ∣ a ∨ a ∣ b := by
  obtain ⟨k, hk⟩ := h
  refine hD a b ⟨M, ?_⟩
  rw [hk]
  exact Ideal.mul_mem_right k _ (Ideal.subset_span (by simp))

theorem first_slope : ∀ {S : Type} [CommRing S] (ϖ : S), Dich ϖ → Roots ϖ → ∀ (q : ℕ → S) (d M : ℕ),
    0 < d → q d = 1 → q 0 ∣ ϖ ^ M → ∃ c : S, (∀ i, 1 ≤ i → i ≤ d → q 0 ∣ q i * c ^ i) ∧
      ∃ i, 1 ≤ i ∧ i ≤ d ∧ q i * c ^ i ∣ q 0 := by
  intro S _ ϖ hD hR q d M hd hqd h0
  classical
  have hex : ∀ j : ℕ, ∃ s : S, (1 ≤ j → q j ∣ q 0 → ∃ u : Sˣ, q 0 = q j * (↑u * s ^ j)) := by
    intro j
    by_cases hj : 1 ≤ j ∧ q j ∣ q 0
    · obtain ⟨t, ht⟩ := hj.2
      have htd : t ∣ ϖ ^ M := (Dvd.intro_left (q j) ht.symm).trans h0
      obtain ⟨r, u, hru⟩ := hR t M j htd (by omega)
      exact ⟨r, fun _ _ => ⟨u, by rw [ht, hru]⟩⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hj⟩
  choose s hs using hex
  set T := (Finset.Icc 1 d).filter (fun j => q j ∣ q 0) with hTdef
  have hmemT : ∀ j, j ∈ T ↔ (1 ≤ j ∧ j ≤ d) ∧ q j ∣ q 0 := by
    intro j
    rw [hTdef, Finset.mem_filter, Finset.mem_Icc]
  have hdT : d ∈ T := (hmemT d).mpr ⟨⟨hd, le_refl d⟩, by rw [hqd]; exact one_dvd _⟩
  have hsdvd : ∀ j ∈ T, s j ∣ ϖ ^ M := by
    intro j hj
    obtain ⟨⟨hj1, _⟩, hjq⟩ := (hmemT j).mp hj
    obtain ⟨u, hu⟩ := hs j hj1 hjq
    have h1 : s j ^ j ∣ q 0 := ⟨q j * ↑u, by rw [hu]; ring⟩
    exact ((dvd_pow_self (s j) (by omega)).trans h1).trans h0
  have hcomp : ∀ i ∈ T, ∀ j ∈ T, s i ∣ s j ∨ s j ∣ s i := by
    intro i hi j _
    exact (dich_of_dvd hD (b := s j) (hsdvd i hi)).symm
  obtain ⟨i₀, hi₀T, hmax⟩ := exists_dvd_all T ⟨d, hdT⟩ s hcomp
  obtain ⟨⟨hi₀1, hi₀d⟩, hi₀q⟩ := (hmemT i₀).mp hi₀T
  refine ⟨s i₀, ?_, i₀, hi₀1, hi₀d, ?_⟩
  · intro i hi1 hid
    rcases dich_of_dvd hD (b := q i) h0 with h | h
    · have hiT : i ∈ T := (hmemT i).mpr ⟨⟨hi1, hid⟩, h⟩
      obtain ⟨u, hu⟩ := hs i hi1 h
      have h2 : q 0 ∣ q i * s i ^ i := by
        rw [hu, mul_left_comm, Units.mul_left_dvd]
      obtain ⟨k, hk⟩ := hmax i hiT
      exact h2.trans ⟨k ^ i, by rw [hk, mul_pow]; ring⟩
    · exact dvd_mul_of_dvd_left h _
  · obtain ⟨u, hu⟩ := hs i₀ hi₀1 hi₀q
    exact ⟨↑u, by rw [hu]; ring⟩

end GlobalTheory.CompanionTheory.NewtonSlope
