import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt

theorem UpperTheory.V.Af.Rs.charEq2 :
    UpperTheory.V.Af.Rs.Core → UpperTheory.V.Af.Rs.Deplete → UpperTheory.V.Af.Rs.CharEq2 := by
  intro hCore hDep k N M _ _ hk χ ψ g h hev
  rw [Filter.eventually_cofinite] at hev
  obtain ⟨B, hB⟩ := hev.bddAbove
  obtain ⟨L, hL⟩ : ∃ L, L = N * M * B.factorial := ⟨_, rfl⟩
  haveI : NeZero L := ⟨by
    rw [hL]
    exact Nat.mul_ne_zero (Nat.mul_ne_zero (NeZero.ne N) (NeZero.ne M)) (Nat.factorial_ne_zero B)⟩
  haveI : NeZero (L * L) := ⟨Nat.mul_ne_zero (NeZero.ne L) (NeZero.ne L)⟩
  have hNL : N ∣ L := ⟨M * B.factorial, by rw [hL]; ring⟩
  have hML : M ∣ L := ⟨N * B.factorial, by rw [hL]; ring⟩
  obtain ⟨χ1, g1, hg1⟩ := hDep k N L hk hNL χ g
  obtain ⟨χ2, h1, hh1⟩ := hDep k M L hk hML ψ h
  have good : ∀ p, Nat.Prime p → ¬ p ∣ L → (h.a p = g.a p ∧ (starRingEnd ℂ) (g.a p) * χ p = g.a p ∧
      (starRingEnd ℂ) (h.a p) * ψ p = h.a p) := by
    intro p hp hpL
    by_contra hbad
    have hle : p ≤ B := hB (by simp only [Set.mem_setOf_eq]; exact fun H => hbad (H hp))
    exact hpL (hL ▸ Dvd.dvd.mul_left (Nat.dvd_factorial hp.pos hle) _)
  have hcore := hCore k (L * L) hk χ1 χ2 g1 h1 ?_ ?_
  · rw [Filter.eventually_cofinite]
    apply ((Finset.range (L + 1)).finite_toSet).subset
    intro p hp
    simp only [Set.mem_setOf_eq] at hp
    by_cases hpL : p ∣ L
    · simp only [Finset.coe_range, Set.mem_Iio]
      exact Nat.lt_succ_of_le (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne L)) hpL)
    · exfalso
      apply hp
      intro hpp
      rw [← ((hg1 p hpp).1 hpL).1, ← ((hh1 p hpp).1 hpL).1, hcore]
  · intro p hp
    by_cases hpL : p ∣ L
    · rw [(hg1 p hp).2 hpL, (hh1 p hp).2 hpL]
    · rw [((hh1 p hp).1 hpL).2, ((hg1 p hp).1 hpL).2]
      exact (good p hp hpL).1
  · intro p hp hne
    by_cases hpL : p ∣ L
    · exact (hg1 p hp).2 hpL
    · obtain ⟨e1, e2, e3⟩ := good p hp hpL
      rw [((hg1 p hp).1 hpL).2]
      by_contra ha
      apply hne
      rw [((hg1 p hp).1 hpL).1, ((hh1 p hp).1 hpL).1]
      rw [e1] at e3
      have hc : (starRingEnd ℂ) (g.a p) ≠ 0 := by simpa using ha
      exact mul_left_cancel₀ hc (e2.trans e3.symm)
